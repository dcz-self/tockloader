"""
Main Tockloader interface.

All high-level logic is contained here. All board-specific or communication
channel specific code is in other files.
"""

import binascii
import contextlib
import copy
import ctypes
import functools
import itertools
import logging
import os
import platform
import string
import textwrap
import time

from . import helpers
from .app_installed import InstalledApp
from .app_padding import PaddingApp
from .app_padding import InstalledPaddingApp
from .app_tab import TabApp
from .board_interface import BoardInterface
from .bootloader_serial import BootloaderSerial
from .exceptions import TockLoaderException
from .tbfh import TBFHeader
from .jlinkexe import JLinkExe
from .openocd import OpenOCD, collect_temp_files
from .flash_file import FlashFile


class TockLoader:
    """
    Implement all Tockloader commands. All logic for how apps are arranged
    is contained here.
    """

    # Tockloader includes built-in settings for known Tock boards to make the
    # overall user experience easier. As new boards support Tock, board-specific
    # options can be include in the Tockloader source to make it easier for
    # users.
    #
    # There are two levels of board-specific configurations: communication
    # details and application details.
    #
    # - Communication details: These are specifics about how Tockloader should
    #   communicate with the board and what specific commands are needed to
    #   program the device.
    #
    # - Application details: These are specifics about how applications should
    #   be situated in flash for a particular board. For instance, MPU rules may
    #   dictate where an application can be placed to properly protect its
    #   memory.
    #
    # Here, we set the application details that are board specific. See
    # `board_interface.py` for the board-specific communication details.
    #
    # Settings are applied iteratively:
    #
    # 1. Default settings
    # 2. General architecture-specific settings (i.e. "cortex-m")
    # 3. Specific architecture-specific settings (i.e. "cortex-m4")
    # 4. Board-specific settings
    #
    # Options
    # -------
    # - `start_address`:   The absolute address in flash where apps start and
    #                      must be loaded.
    # - `order`:           How apps should be sorted when flashed onto the board.
    #                      Supported values: size_descending, None
    # - `size_constraint`: Valid sizes for the entire application.
    #                      Supported values: powers_of_two, (multiple, value),
    #                                        None
    # - `alignment_constraint`: If apps have to be aligned to some value.
    #                      Supported values: size, None
    # - `cmd_flags`:       A dict of command line flags and the value they
    #                      should be set to for the board.
    TOCKLOADER_APP_SETTINGS = {
        "default": {
            "start_address": 0x30000,
            "order": None,
            "size_constraint": None,
            "alignment_constraint": None,
            "cmd_flags": {},
        },
        "arch": {
            "cortex-m": {
                "order": "size_descending",
                "size_constraint": "powers_of_two",
                "alignment_constraint": "size",
            }
        },
        "boards": {
            "arty": {
                "start_address": 0x40430000,
            },
            "edu-ciaa": {
                "start_address": 0x1A040000,
                "cmd_flags": {"bundle_apps": True, "openocd": True},
            },
            "hifive1": {"start_address": 0x20430000},
            "hifive1b": {"start_address": 0x20040000},
            "litex_arty": {"start_address": 0x41000000},
            "litex_sim": {"start_address": 0x00080000},
            "nucleof4": {"start_address": 0x08040000},
            "microbit_v2": {"start_address": 0x00040000},
            "stm32f3discovery": {"start_address": 0x08020000},
            "stm32f4discovery": {"start_address": 0x08040000},
            "raspberry_pi_pico": {"start_address": 0x10020000},
        },
    }

    def __init__(self, args):
        self.args = args

        # These are customized once we have a connection to the board and know
        # what board we are talking to.
        self.app_settings = self.TOCKLOADER_APP_SETTINGS["default"]

        # If the user specified a board manually, we might be able to update
        # options now, so we can try.
        self._update_board_specific_options()

    def open(self):
        """
        Select and then open the correct channel to talk to the board.

        For the bootloader, this means opening a serial port. For JTAG, not much
        needs to be done.
        """

        # Verify only one of openocd, jlink, flash file, or serial are set.
        if (
            len(
                list(
                    filter(
                        lambda a: a != False,
                        [
                            getattr(self.args, "jlink", False),
                            getattr(self.args, "openocd", False),
                            getattr(self.args, "flash_file") != None,
                            getattr(self.args, "serial", False),
                        ],
                    )
                )
            )
            > 1
        ):
            raise TockLoaderException(
                "Can only use one of --jlink, --openocd, --flash-file or --serial options"
            )

        # Get an object that allows talking to the board.
        if hasattr(self.args, "jlink") and self.args.jlink:
            # User passed `--jlink`. Force the jlink channel.
            self.channel = JLinkExe(self.args)
        elif hasattr(self.args, "openocd") and self.args.openocd:
            # User passed `--openocd`. Force the OpenOCD channel.
            self.channel = OpenOCD(self.args)
        elif hasattr(self.args, "serial") and self.args.serial:
            # User passed `--serial`. Force the serial bootloader channel.
            self.channel = BootloaderSerial(self.args)
        elif hasattr(self.args, "flash_file") and self.args.flash_file is not None:
            # User passed `--flash-file` option with an associated file. Force
            # operation on the specified file.
            self.channel = FlashFile(self.args)
        else:
            # Try to do some magic to determine the correct channel to use. Our
            # goal is to automatically choose the correct setting so that
            # `tockloader` just works without having to specify a board and any
            # flags.

            # Loop so we can `break`. This will never execute more than once.
            while True:

                # One issue is that JTAG connections often expose both a JTAG
                # and a serial port. So, if we try to use the serial port first
                # we will incorrectly detect that serial port. So, we start with
                # the less likely jtag channel. We start with jlinkexe because
                # it has been in tockloader longer. Let me know if this is the
                # wrong decision.
                jlink_channel = JLinkExe(self.args)
                if jlink_channel.attached_board_exists():
                    self.channel = jlink_channel
                    logging.info("Using jlink channel to communicate with the board.")
                    break

                # Next try openocd.
                openocd_channel = OpenOCD(self.args)
                if openocd_channel.attached_board_exists():
                    self.channel = openocd_channel
                    logging.info("Using openocd channel to communicate with the board.")
                    break

                # Default to using the serial bootloader. This is how tockloader
                # has worked for a long time. We may want to change this, but
                # for now we don't change the default behavior.
                self.channel = BootloaderSerial(self.args)

                # Exit while(1) loop, do not remove this break!
                break

        # And make sure the channel is open (e.g. open a serial port).
        self.channel.open_link_to_board()

    def flash_binary(self, binary, address, pad=None):
        """
        Tell the bootloader to save the binary blob to an address in internal
        flash.

        This will pad the binary as needed, so don't worry about the binary
        being a certain length.

        This accepts an optional `pad` parameter. If used, the `pad` parameter
        is a tuple of `(length, value)` signifying the number of bytes to pad,
        and the particular byte to use for the padding.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Check if we should add padding, which is just pad[0] copies of the
            # same byte (pad[1]).
            if pad:
                extra = bytes([pad[1]] * pad[0])
                binary = binary + extra

            self.channel.flash_binary(address, binary)

            # Flash command can optionally set attributes.
            if self.args.set_attribute != None:
                for k, v in self.args.set_attribute:
                    logging.debug("Setting attribute {}={}".format(k, v))
                    ret = self._set_attribute(k, v, log_status=False)

                    if ret:
                        logging.debug("Unable to set attribute after flash command.")
                        logging.debug(ret)

    def list_apps(self, verbose, quiet):
        """
        Query the chip's flash to determine which apps are installed.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Get all apps based on their header
            apps = self._extract_all_app_headers(verbose)

            self._print_apps(apps, verbose, quiet)

    def install(self, tabs, replace="yes", erase=False, sticky=False):
        """
        Add or update TABs on the board.

        - `replace` can be "yes", "no", or "only"
        - `erase` if true means erase all other apps before installing
        """
        # Check if we have any apps to install. If not, then we can quit early.
        if len(tabs) == 0:
            raise TockLoaderException("No TABs to install")

        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # This is the architecture we need for the board.
            arch = self.channel.get_board_arch()
            if arch == None:
                raise TockLoaderException(
                    "Need known arch to install apps. Perhaps use `--arch` flag."
                )

            # Start with the apps we are searching for.
            replacement_apps = self._extract_apps_from_tabs(tabs, arch)

            # If we want to install these as sticky apps, mark that now.
            if sticky:
                logging.info("Marking apps as sticky.")
                for app in replacement_apps:
                    app.set_sticky()

            # Get a list of installed apps
            existing_apps = self._extract_all_app_headers()

            # What apps we want after this command completes
            resulting_apps = []

            # Whether we actually made a change or not
            changed = False

            # If we want to erase first, loop through looking for non sticky
            # apps and remove them from the existing app list.
            if erase:
                new_existing_apps = []
                for existing_app in existing_apps:
                    if existing_app.is_sticky():
                        new_existing_apps.append(existing_app)
                if len(existing_apps) != len(new_existing_apps):
                    changed = True
                existing_apps = new_existing_apps

            # Check to see if this app is in there
            if replace == "yes" or replace == "only":
                for existing_app in existing_apps:
                    for replacement_app in replacement_apps:
                        if existing_app.get_name() == replacement_app.get_name():
                            resulting_apps.append(copy.deepcopy(replacement_app))
                            changed = True
                            break
                    else:
                        # We did not find a replacement app. That means we want
                        # to keep the original.
                        resulting_apps.append(existing_app)

                # Now, if we want a true install, and not an update, make sure
                # we add all apps that did not find a replacement on the board.
                if replace == "yes":
                    for replacement_app in replacement_apps:
                        for resulting_app in resulting_apps:
                            if replacement_app.get_name() == resulting_app.get_name():
                                break
                        else:
                            # We did not find the name in the resulting apps.
                            # Add it.
                            resulting_apps.append(replacement_app)
                            changed = True

            elif replace == "no":
                # Just add the apps
                resulting_apps = existing_apps + replacement_apps
                changed = True

            if changed:
                # Since something is now different, update all of the apps
                self._reshuffle_apps(resulting_apps)
            else:
                # Nothing changed, so we can raise an error
                raise TockLoaderException("Nothing found to update")

    def uninstall_app(self, app_names):
        """
        If an app by this name exists, remove it from the chip. If no name is
        given, present the user with a list of apps to remove.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Get a list of installed apps
            apps = self._extract_all_app_headers()

            # If the user didn't specify an app list...
            if len(app_names) == 0:
                if len(apps) == 0:
                    raise TockLoaderException("No apps are installed on the board")
                elif len(apps) == 1:
                    # If there's only one app, delete it
                    app_names = [apps[0].get_name()]
                    logging.info("Only one app on board.")
                else:
                    options = ["** Delete all"]
                    options.extend([app.get_name() for app in apps])
                    name = helpers.menu(
                        options,
                        return_type="value",
                        prompt="Select app to uninstall ",
                        title="There are multiple apps currently on the board:",
                    )
                    if name == "** Delete all":
                        app_names = [app.get_name() for app in apps]
                    else:
                        app_names = [name]

            logging.status("Attempting to uninstall:")
            for app_name in app_names:
                logging.status("  - {}".format(app_name))

            #
            # Uninstall apps by replacing their TBF header with one that is just
            # padding for the same total size.
            #

            # Get a list of apps to remove respecting the sticky bit.
            remove_apps = []
            for app in apps:
                # Only remove apps that are marked for uninstall, unless they
                # are sticky without force being set.
                if app.get_name() in app_names:
                    if app.is_sticky():
                        if self.args.force:
                            logging.info(
                                'Removing sticky app "{}" because --force was used.'.format(
                                    app
                                )
                            )
                            remove_apps.append(app)
                        else:
                            logging.info(
                                'Not removing app "{}" because it is sticky.'.format(
                                    app
                                )
                            )
                            logging.info(
                                "To remove this you need to include the --force option."
                            )
                    else:
                        # Normal uninstall
                        remove_apps.append(app)

            if len(remove_apps) > 0:
                # Uninstall apps by replacing them all with padding.
                for remove_app in remove_apps:
                    self._replace_with_padding(remove_app)

                logging.status("Uninstall complete.")

                if self.args.debug:
                    # And let the user know the state of the world now that we're done
                    apps = self._extract_all_app_headers()
                    if len(apps):
                        logging.info(
                            "After uninstall, remaining apps on board: ", end=""
                        )
                        self._print_apps(apps, verbose=False, quiet=True)
                    else:
                        logging.info("After uninstall, no apps on board.")

            else:
                raise TockLoaderException(
                    "Could not find any apps on the board to uninstall."
                )

    def erase_apps(self):
        """
        Erase flash where apps go. All apps are not actually cleared, we just
        overwrite the header of the first app.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # On force we can just eliminate all apps
            if self.args.force:
                # Erase the first page where apps go. This will cause the first
                # header to be invalid and effectively removes all apps.
                address = self._get_apps_start_address()
                self.channel.clear_bytes(address)

            else:
                # Get a list of installed apps
                apps = self._extract_all_app_headers()

                keep_apps = []
                for app in apps:
                    if app.is_sticky():
                        keep_apps.append(app)
                        logging.info(
                            'Not erasing app "{}" because it is sticky.'.format(app)
                        )

                if len(keep_apps) == 0:
                    address = self._get_apps_start_address()
                    self.channel.clear_bytes(address)

                    logging.info("All apps have been erased.")
                else:
                    self._reshuffle_apps(keep_apps)

                    logging.info("After erasing apps, remaining apps on board: ")
                    self._print_apps(apps, verbose=False, quiet=True)

    def set_flag(self, app_names, flag_name, flag_value):
        """
        Set a flag in the TBF header.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Get a list of installed apps
            apps = self._extract_all_app_headers()

            if len(apps) == 0:
                raise TockLoaderException("No apps are installed on the board")

            # User did not specify apps. Pick from list.
            if len(app_names) == 0:
                options = ["** All"]
                options.extend([app.get_name() for app in apps])
                name = helpers.menu(
                    options,
                    return_type="value",
                    prompt="Select app to configure ",
                    title="Which apps to configure?",
                )
                if name == "** All":
                    app_names = [app.get_name() for app in apps]
                else:
                    app_names = [name]

            # Configure all selected apps
            changed = False
            for app in apps:
                if app.get_name() in app_names:
                    app.get_header().set_flag(flag_name, flag_value)
                    changed = True

            if changed:
                self._reshuffle_apps(apps)
                logging.info(
                    'Set flag "{}" to "{}" for apps: {}'.format(
                        flag_name, flag_value, ", ".join(app_names)
                    )
                )
            else:
                logging.info("No matching apps found. Nothing changed.")

    def list_attributes(self):
        """
        Download all attributes stored on the board.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            if not self._bootloader_is_present():
                raise TockLoaderException(
                    "No bootloader found! That means there is nowhere for attributes to go."
                )

            self._print_attributes(self.channel.get_all_attributes())

    def set_attribute(self, key, value):
        """
        Change an attribute stored on the board.
        """

        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Use helper function to do all of the work.
            ret = self._set_attribute(key, value)

            if ret:
                # Some error occurred!
                raise TockLoaderException(ret)

    def remove_attribute(self, key):
        """
        Remove an existing attribute already stored on the board.
        """
        # Do some checking
        if len(key.encode("utf-8")) > 8:
            raise TockLoaderException("Key is too long. Must be 8 bytes or fewer.")

        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            if not self._bootloader_is_present():
                raise TockLoaderException(
                    "No bootloader found! That means there is nowhere for attributes to go."
                )

            # Create a null buffer to overwrite with
            out = bytes([0] * 9)

            # Find if this attribute key already exists
            for index, attribute in enumerate(self.channel.get_all_attributes()):
                if attribute and attribute["key"] == key:
                    logging.status(
                        "Found existing key at slot {}. Removing.".format(index)
                    )
                    self.channel.set_attribute(index, out)
                    break
            else:
                raise TockLoaderException("Error: Attribute does not exist.")

    def set_start_address(self, address):
        """
        Set the address that the bootloader jumps to to run kernel code.
        """

        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            if not self._bootloader_is_present():
                raise TockLoaderException(
                    "No bootloader found! That means there is nowhere for attributes to go."
                )

            self.channel.set_start_address(address)

    def info(self):
        """
        Print all info about this board.
        """
        # Enter bootloader mode to get things started
        with self._start_communication_with_board():

            # Print all apps
            print("Apps:")
            apps = self._extract_all_app_headers()
            self._print_apps(apps, True, False)

            if self._bootloader_is_present():
                # Print all attributes
                print("Attributes:")
                attributes = self.channel.get_all_attributes()
                self._print_attributes(attributes)
                print("")

                # Show bootloader version
                version = self.channel.get_bootloader_version()
                if version == None:
                    version = "unknown"
                print("Bootloader version: {}".format(version))
            else:
                print("No bootloader.")

    def dump_flash_page(self, page_num):
        """
        Print one page of flash contents.
        """
        with self._start_communication_with_board():
            page_size = self.channel.get_page_size()
            address = page_size * page_num
            print("Page number: {} ({:#08x})".format(page_num, address))

            flash = self.channel.read_range(address, page_size)
            self._print_flash(address, flash)

    def read_flash(self, address, length):
        """
        Print some flash contents.
        """
        with self._start_communication_with_board():
            flash = self.channel.read_range(address, length)
            self._print_flash(address, flash)

    def write_flash(self, address, length, value):
        """
        Write a byte to some flash contents.
        """
        with self._start_communication_with_board():
            to_write = bytes([value] * length)
            self.channel.flash_binary(address, to_write, pad=False)

    def run_terminal(self):
        """
        Create an interactive terminal session with the board.

        This is a special-case use of Tockloader where this is really a helper
        function for running some sort of underlying terminal-like operation.
        Therefore, how we set this up is a little different from other
        tockloader commands. In particular, we do _not_ want `tockloader.open()`
        to have been called at this point.
        """
        # By default, we use the serial connection and serial terminal. However,
        # tockloader supports other terminals, and we choose the correct one
        # here. There is no need to save the channel, since
        # `channel.run_terminal()` never returns.
        if self.args.rtt:
            if self.args.openocd:
                channel = OpenOCD(self.args)
            else:
                channel = JLinkExe(self.args)

        else:
            channel = BootloaderSerial(self.args)
            channel.open_link_to_board(listen=True)

        channel.run_terminal()

    def print_known_boards(self):
        """
        Simple function to print to console the boards that are hardcoded
        into Tockloader to make them easier to use.
        """
        BoardInterface(self.args).print_known_boards()

    ############################################################################
    ## Internal Helper Functions for Communicating with Boards
    ############################################################################

    @contextlib.contextmanager
    def _start_communication_with_board(self):
        """
        Based on the transport method used, there may be some setup required
        to connect to the board. This function runs the setup needed to connect
        to the board. It also times the operation.

        For the bootloader, the board needs to be reset and told to enter the
        bootloader mode. For JTAG, this is unnecessary.
        """
        # Time the operation
        then = time.time()
        try:
            if not self.args.no_bootloader_entry:
                logging.debug("start: Enter bootloader mode")
                self.channel.enter_bootloader_mode()
            else:
                time.sleep(0.2)

            # Now that we have connected to the board and the bootloader
            # if necessary, make sure we know what kind of board we are
            # talking to.
            logging.debug("start: Determine current board")
            self.channel.determine_current_board()

            # Set any board-specific options that tockloader needs to use.
            logging.debug("start: Update board specific options")
            self._update_board_specific_options()

            yield

            if platform.system() == "Windows":
                for file in collect_temp_files:
                    os.remove(file)

            now = time.time()
            logging.info("Finished in {:0.3f} seconds".format(now - then))
        except Exception as e:
            raise (e)
        finally:
            self.channel.exit_bootloader_mode()

    def _bootloader_is_present(self):
        """
        Check if a bootloader exists on this board. It is specified by the
        string "TOCKBOOTLOADER" being at address 0x400.
        """
        # Check to see if the channel already knows this. For example,
        # if you are connected via a serial link to the bootloader,
        # then obviously the bootloader is present.
        if self.channel.bootloader_is_present() == True:
            return True

        # Otherwise check for the bootloader flag in the flash.

        # Constants for the bootloader flag
        address = 0x400
        length = 14
        flag = self.channel.read_range(address, length)
        flag_str = flag.decode("utf-8", "ignore")
        logging.debug("Read from flags location: {}".format(flag_str))
        return flag_str == "TOCKBOOTLOADER"

    def _update_board_specific_options(self):
        """
        This uses the name of the board to update any hard-coded options about
        how Tockloader should function. This is a convenience mechanism, as it
        prevents users from having to pass them in through command line arguments.
        """

        # Get the arch and name of the board if they are known.
        arch = None
        board = None
        if hasattr(self, "channel"):
            # We have configured a channel to a board, and that channel may
            # have read off of the board which board it actually is.
            arch = self.channel.get_board_arch()
            board = self.channel.get_board_name()
        else:
            arch = getattr(self.args, "arch", None)
            board = getattr(self.args, "board", None)

        # Start by updating settings using the architecture.
        if arch:
            # Loop through the arch string for generic versions.
            for i in range(4, len(arch) + 1):
                try_arch = arch[0:i]
                if try_arch in self.TOCKLOADER_APP_SETTINGS["arch"]:
                    self.app_settings.update(
                        self.TOCKLOADER_APP_SETTINGS["arch"][try_arch]
                    )
                    # Remove the options so they do not get set twice.
                    del self.TOCKLOADER_APP_SETTINGS["arch"][try_arch]

        # Configure settings for the board if possible.
        if board and board in self.TOCKLOADER_APP_SETTINGS["boards"]:
            self.app_settings.update(self.TOCKLOADER_APP_SETTINGS["boards"][board])
            # Remove the options so they do not get set twice.
            del self.TOCKLOADER_APP_SETTINGS["boards"][board]

        # Allow boards to specify command line arguments by default so that
        # users do not have to pass them in every time.
        if "cmd_flags" in self.app_settings:
            for flag, setting in self.app_settings["cmd_flags"].items():
                logging.info(
                    'Hardcoding command line argument "{}" to "{}" for board {}.'.format(
                        flag, setting, board
                    )
                )
                setattr(self.args, flag, setting)

    def _get_apps_start_address(self):
        """
        Return the address in flash where applications start on this platform.
        This might be set on the board itself, in the command line arguments
        to Tockloader, or just be the default.
        """

        # First check if we have a cached value. We might need to lookup the
        # start address a lot, so we don't want to have to query the board for
        # it each time. We also do not use `self.app_settings['start_address']`
        # as the cache because a board attribute may supersede it, and we don't
        # have a good way to mark it as unset since
        # app_settings['start_address'] is set by default.
        cached = getattr(self, "apps_start_address", None)
        if cached:
            return cached

        # Highest priority is the command line argument. If the user specifies
        # that, we use that unconditionally.
        cmdline_app_address = getattr(self.args, "app_address", None)
        if cmdline_app_address:
            self.apps_start_address = cmdline_app_address
            return cmdline_app_address

        # Next we check if the attached board has an attribute that can tell us.
        if self.channel:
            attributes = self.channel.get_all_attributes()
            for attribute in attributes:
                if attribute and attribute["key"] == "appaddr":
                    self.apps_start_address = int(attribute["value"], 0)
                    return self.apps_start_address

        # Lastly we default to what was configured using the
        # `TOCKLOADER_APP_SETTINGS` variable.
        return self.app_settings["start_address"]

    ############################################################################
    ## Helper Functions for Shared Code
    ############################################################################

    def _set_attribute(self, key, value, log_status=True):
        """
        Internal function for setting an attribute stored on the board.

        Bootloader mode must be active.

        Returns None if successful and an error string if not.
        """
        # By default log status. However, that is not always appropriate, so
        # if `log_status` is False then send that to debug output.
        logging_fn = logging.status
        if log_status == False:
            logging_fn = logging.debug

        # Do some checking
        if len(key.encode("utf-8")) > 8:
            return "Key is too long. Must be 8 bytes or fewer."
        if len(value.encode("utf-8")) > 55:
            return "Value is too long. Must be 55 bytes or fewer."

        # Check for the bootloader, and importantly the attributes section.
        if not self._bootloader_is_present():
            return (
                "No bootloader found! That means there is nowhere for attributes to go."
            )

        # Create the buffer to write as the attribute
        out = bytes([])
        # Add key
        out += key.encode("utf-8")
        out += bytes([0] * (8 - len(out)))
        # Add length
        out += bytes([len(value.encode("utf-8"))])
        # Add value
        out += value.encode("utf-8")

        # Find if this attribute key already exists
        open_index = -1
        for index, attribute in enumerate(self.channel.get_all_attributes()):
            if attribute:
                if attribute["key"] == key:
                    if attribute["value"] == value:
                        logging_fn(
                            "Found existing key,value at slot {}. Nothing to do.".format(
                                index
                            )
                        )
                    else:
                        logging_fn(
                            "Found existing key at slot {}. Overwriting.".format(index)
                        )
                        self.channel.set_attribute(index, out)
                    break
            else:
                # Save where we should put this attribute if it does not
                # already exist.
                if open_index == -1:
                    open_index = index
        else:
            if open_index == -1:
                return "No open space to save this attribute."
            else:
                logging_fn(
                    "Key not found. Writing new attribute to slot {}".format(open_index)
                )
                self.channel.set_attribute(open_index, out)

    ############################################################################
    ## Helper Functions for Manipulating Binaries and TBF
    ############################################################################

    def _reshuffle_apps(self, apps):
        """
        Given an array of apps, some of which are new and some of which exist,
        find how they can fit in the flash together, and write them.

        This function is really the driver of tockloader, and is responsible for
        setting up applications in a way that can be successfully used by the
        board.
        """
        from . import allocate
 
        # Get where the apps live in flash.
        start_address = self._get_apps_start_address()
        # HACK! Let's assume no board has more than 2 MB of flash.
        end_address = start_address + 0x200000

        solver_apps = [
            allocate.FixedApp(
                app.get_name(),
                app.get_size(),
                isinstance(app, InstalledApp),
                [start for start, size in app.get_fixed_addresses_flash_and_sizes()]
            )
            if app.has_fixed_addresses()
            else allocate.App(app.get_name(), app.get_size(), False)
            for app in apps
        ]
        # HACK: this only works for Cortex-M, for demonstration purposes.
        solution = allocate.solve_flash(start_address, end_address, 1024, solver_apps)
        if solution is None:
            logging.error("Unable to find a valid placement solution to flash apps.")
            return

        placements = [(app, solution.get_placement(app.get_name())) for app in apps]

        for app, placement in placements:
            print(
                repr(app.get_name()),
                "placed at: 0x{:x}, size 0x{:x}"
                    .format(*placement)
            )
        
        ordered_apps = list(sorted(placements, key=lambda a: a[1]))
        
        last_end = start_address
        apps_with_gaps = []
        for app, (start, size) in ordered_apps:
            # We don't track which padding apps are installed,
            # so let's flash all of them.
            if last_end != start:
                # Tock detects apps by valid tbf headers, one after another.
                # An area between apps needsits own header,
                # or the kernel will stop scanning.
                gap_size = start - last_end
                apps_with_gaps.append(
                    (PaddingApp(gap_size), last_end, gap_size)
                )
                
            # Flash only apps that are new or need to be modified.
            # The only way an app needs to be modified is if it's installed
            # and its new start is different than the old one.
            if (
                not isinstance(app, InstalledApp)
                # Installed app got moved
                or app.get_address() != start
            ):
                try:
                    print("address", app.get_address())
                except:
                    pass
                apps_with_gaps.append((app, start, size))
            last_end = start + size

        for a, start, size in apps_with_gaps:
            try:
                name = a.get_name()
            except:
                name = 'pad'
            print(name, "0x{:x}, 0x{:x}".format(start, size))

        # Apps already on the board may get a new address.
        # Read their data before flashing,
        # or it may get overwritten prematurely by the flashing itself!
        binaries = [(start, app.get_binary(start, size, self.channel))
            for app, start, size in apps_with_gaps]

        dry = False
        if not dry:
            # Actually write apps to the board.
            for start, binary in binaries:
                self.channel.flash_binary(start, binary)
            
            if last_end:
                # Then erase the next page if we have not already rewritten all
                # existing apps. This ensures that flash is clean at the end of the
                # installed apps and makes sure the kernel will find the correct end
                # of applications.
                self.channel.clear_bytes(last_end)

        return

    def _replace_with_padding(self, app):
        """
        Update the TBF header of installed app `app` with a padding header
        to effectively uninstall it.
        """
        # Create replacement padding app.
        size = app.get_size()
        padding = PaddingApp(size)
        address = app.get_address()

        logging.debug(
            "Flashing padding app header (total size:{}) at {:#x} to uninstall {}".format(
                size, address, app
            )
        )
        self.channel.flash_binary(address, padding.get_tbfh().get_binary())

    def _extract_all_app_headers(self, verbose=False):
        """
        Iterate through the flash on the board for the header information about
        each app.
        """
        apps = []

        # This can be the default, it can be configured in the attributes on
        # the hardware, or it can be passed in to Tockloader.
        address = self._get_apps_start_address()

        # Jump through the linked list of apps
        while True:
            header_length = 200  # Version 2
            logging.debug(
                "Reading for app header @{:#x}, {} bytes".format(address, header_length)
            )
            flash = self.channel.read_range(address, header_length)

            print('flash')
            # if there was an error, the binary array will be empty
            if len(flash) < header_length:
                print('err')
                break

            # Get all the fields from the header
            tbfh = TBFHeader(flash)
            print("hdr")
            if tbfh.is_valid():
                if tbfh.is_app():
                    print('app')
                    app = InstalledApp(tbfh, address)
                    apps.append(app)
                else:
                    print('padding')
                    print(tbfh)
                    app = InstalledPaddingApp(tbfh, address)
                    if verbose:
                        # In verbose mode include padding
                        apps.append(app)

                address += app.get_size()

            else:
                print('invalid')
                break

        if self.args.debug:
            logging.debug(
                "Found {} app{} on the board.".format(
                    len(apps), helpers.plural(len(apps))
                )
            )
            for i, app in enumerate(apps):
                logging.debug("  {}. {}".format(i + 1, app))

        return apps

    def _extract_apps_from_tabs(self, tabs, arch):
        """
        Iterate through the list of TABs and create the app object for each.
        """
        apps = []

        for tab in tabs:
            # Check if this app is specifically marked as compatible with
            # certain boards, and if so, if the board being programmed is one of
            # them.
            if not self.args.force and not tab.is_compatible_with_board(
                self.channel.get_board_name()
            ):
                # App is marked for certain boards, and this is not one.
                logging.info(
                    'App "{}" is not compatible with your board.'.format(
                        tab.get_app_name()
                    )
                )
                if self.args.debug:
                    logging.debug(
                        'Supported boards for app "{}":'.format(tab.get_app_name())
                    )
                    for board in tab.get_compatible_boards():
                        logging.debug("- {}".format(board))
                continue

            # Check if this app was compiled for the version of the Tock kernel
            # currently on the board. If not, print a notice.
            if not self.args.force and not tab.is_compatible_with_kernel_version(
                self.channel.get_kernel_version()
            ):
                # App needs a different kernel version than what is on the board.
                logging.info(
                    'App "{}" requires kernel version "2", but tockloader determined your kernel version is "{}".'.format(
                        tab.get_app_name(), self.channel.get_kernel_version()
                    )
                )
                continue

            # This app is good to install, continue the process.

            app = tab.extract_app(arch)

            # Enforce other sizing constraints here.
            app.set_size_constraint(self.app_settings["size_constraint"])

            apps.append(app)

        if len(apps) == 0:
            raise TockLoaderException(
                "No valid apps for this board were provided. Use --force to override."
            )

        return apps

    def _app_is_aligned_correctly(self, address, size):
        """
        Check if putting an app at this address will be OK with the MPU.
        """
        # The rule for the MPU is that the size of the protected region must be
        # a power of two, and that the region is aligned on a multiple of that
        # size.

        if self.app_settings["size_constraint"]:
            if self.app_settings["size_constraint"] == "powers_of_two":
                # Check if size is not a power of two.
                if (size & (size - 1)) != 0:
                    return False

        if self.app_settings["alignment_constraint"]:
            if self.app_settings["alignment_constraint"] == "size":
                # Check that address is a multiple of size.
                multiple = address // size
                if multiple * size != address:
                    return False

        return True

    ############################################################################
    ## Printing helper functions
    ############################################################################

    def _print_flash(self, address, flash):
        """
        Print binary data in a nice hexdump format.
        """

        def chunks(l, n):
            for i in range(0, len(l), n):
                yield l[i : i + n]

        def dump_line(addr, bytes):
            k = binascii.hexlify(bytes).decode("utf-8")
            b = " ".join(list(chunks(k, 2)))
            if len(b) >= 26:
                # add middle space
                b = "{} {}".format(b[0:24], b[24:])
            # Add right padding for not full lines
            if len(b) < 48:
                b = "{0: <48}".format(b)
            printable = string.ascii_letters + string.digits + string.punctuation + " "
            t = "".join([chr(i) if chr(i) in printable else "." for i in bytes])
            print("{:08x}  {}  |{}|".format(addr, b, t))

        for i, chunk in enumerate(chunks(flash, 16)):
            dump_line(address + (i * 16), chunk)

    def _print_apps(self, apps, verbose, quiet):
        """
        Print information about a list of apps
        """
        if not quiet:
            # Print info about each app
            for i, app in enumerate(apps):
                if app.is_app():
                    print(helpers.text_in_box("App {}".format(i), 52))

                    # Check if this app is OK with the MPU region requirements.
                    if not self._app_is_aligned_correctly(
                        app.get_address(), app.get_size()
                    ):
                        print("  [WARNING] App is misaligned for the MPU")
                        print("0x{:x} sz 0x{:x}".format(app.get_address(), app.get_size()))

                    print(textwrap.indent(app.info(verbose), "  "))
                    print("")
                else:
                    # Display padding
                    print(helpers.text_in_box("Padding", 52))
                    print(textwrap.indent(app.info(verbose), "  "))
                    print("")

            if len(apps) == 0:
                logging.info("No found apps.")

        else:
            # In quiet mode just show the names.
            print(" ".join([app.get_name() for app in apps]))

    def _print_attributes(self, attributes):
        """
        Print the list of attributes in the bootloader.
        """
        for index, attribute in enumerate(attributes):
            if attribute:
                print(
                    "{:02d}: {:>8} = {}".format(
                        index, attribute["key"], attribute["value"]
                    )
                )
            else:
                print("{:02d}:".format(index))
