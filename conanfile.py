from conan import ConanFile
from conan.tools.files import copy


class IntxConan(ConanFile):
    name = "intx"
    version = "0.15.0"
    description = "High‑performance multiprecision integer library for C++"
    url = "https://github.com/intx/intx"
    license = "Apache-2.0"
    topics = ("integer", "multiprecision", "arbitrary-precision", "extended-precision",
              "biginteger", "uint128", "uint256", "uint512")

    package_type = "header-library"
    exports_sources = "include/*"
    no_copy_source = True
    test_package_folder = "test/integration/conan_package"

    def package(self):
        copy(self, "*", self.source_folder, self.package_folder)

    def package_info(self):
        self.cpp_info.bindirs = []
        self.cpp_info.libdirs = []
