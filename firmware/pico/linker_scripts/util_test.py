from util_uf2 import *
from util_crc import *
import os

APPLICATION_BUILD_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "build", "application")
dump_uf2_file(os.path.join(APPLICATION_BUILD_DIR, "application.uf2"))

bin_file_to_uf2_file(os.path.join(APPLICATION_BUILD_DIR, "application.bin"), os.path.join(APPLICATION_BUILD_DIR, "application_test.uf2"))
dump_uf2_file(os.path.join(APPLICATION_BUILD_DIR, "application_test.uf2"))

