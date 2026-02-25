/* Copyright (C) 2017, 2021-2026 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#include <algorithm>
#include <csignal>
#include <csetjmp>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <list>
#include <string>
#include <sstream>
#include <vector>

#include "config.h"

#include "MLI.hh"
#include "database.hh"
#include "database-parser.hh"

#include "reassign.hh"


std::string theory_name;
extern std::string infile_name;  // Defined in database-parser.yy.
std::string outfile_name;
std::string logfile_name;

extern std::vector<std::string> dirs;
extern bool verbose;


// debug.hh
namespace mli {
void precedence_init();
}

int main(int argc, char *argv[], char* envp[]) {

#if 0
  std::unordered_map<std::string, std::string> envs;

  for (char** p = envp; *p != nullptr; ++p) {
    char* sp = strchr(*p, '=');

    // If the '=' is missing, the string is illegal and ignored:
    if (sp != nullptr)
      envs.emplace(std::string(*p, sp), std::string(sp + 1));
  }

  for (auto i: envs)
    std::cout << i.first << " = " << i.second << std::endl;
#endif

#if 0 // debug-mli
  mli::precedence_init();
  return EXIT_SUCCESS;
#endif

  std::vector<std::string> args(argv, argv + argc);

  if (args.size() <= 1) {
    std::cout <<
      "mli: missing operand\n"
      "Try 'mli --help' for more information."
      << std::endl;
    return EXIT_FAILURE;
  }


  bool infile_found = false;
  bool outfile_found = false;
  bool logfile_found = false;

  bool theory_found = false;


  auto i = args.begin();
  ++i;  // Skip program name.

  for (; i != args.end(); ++i) {
    if (*i == "--version") {
      std::cout <<
        PACKAGE_TARNAME << " (" << PACKAGE_NAME << ") " << PACKAGE_VERSION << ", MetaLogic Inference\n"
        "Written by Hans Åberg\n\n"
        "Copyright (C) 2021 Hans Åberg.\n"
        "License GPLv3+: GNU GPL version 3 or later, cf. <https://gnu.org/licenses/gpl.html>\n"
        "Free software: redistribution allowed, also for changed versions.\n"
        "No warranty: to the extent permitted by law.\n"
        << std::flush;
      return EXIT_SUCCESS;
    }

    if (*i == "--help") {
      std::cout <<
        "Usage: mli [OPTION] ... [--input=]FILE\n"
        "Analyze and find proofs of logical and mathematical statements.\n\n"
        "  --help         display this help text, and exit\n"
        "  --version      output version information, and exit\n\n"
        "For processing, an input FILE must be given, with optional prefix --input=\n\n"
        "Optional arguments:\n"
        "  --input=FILE   read input from FILE\n"
        "  --output=FILE  write output to FILE\n"
        "  --log=FILE     write log output to FILE\n"
        "  --include=DIR  add include directory DIR\n"
        "  --theory=NAME  name the input file theory database to NAME\n"
        "  --verbose      more info to standard output\n\n"
        "Report bugs to <mailto:" PACKAGE_BUGREPORT ">.\n"
        PACKAGE_NAME " home page: <" PACKAGE_URL ">.\n"
        "General help using GNU software: <https://www.gnu.org/gethelp/>.\n"
        "Report translation bugs to <https://translationproject.org/team/>.\n"
        "For complete documentation, see manual, in any available format.\n"
        << std::flush;
      return EXIT_SUCCESS;
    }

    if (i->substr(0, 9) == "--verbose") {
      verbose = true;
      continue;
    }

    if (i->substr(0, 9) == "--theory=") {
      if (theory_found) {
        std::cerr <<
          "mli: more than one theory given: \"" << theory_name << "\" and \"" << i->substr(9) << "\"\n"
          << std::endl;
        return EXIT_FAILURE;
      }
      else
        theory_found = true;

      theory_name = i->substr(9);
      continue;
    }

    if (i->substr(0, 8) == "--input=") {
      if (infile_found) {
        std::cerr <<
          "mli: more than one input file given: \"" << infile_name << "\" and \"" << i->substr(8) << "\"\n"
          << std::endl;
        return EXIT_FAILURE;
      }
      else
        infile_found = true;

      infile_name = i->substr(8);
      continue;
    }

    if (i->substr(0, 9) == "--output=") {
      if (outfile_found) {
        std::cerr <<
          "mli: more than one output file given: \"" << outfile_name << "\" and \"" << i->substr(9) << "\"\n"
          << std::endl;
        return EXIT_FAILURE;
      }
      else
        outfile_found = true;

      outfile_name = i->substr(9);
      continue;
    }

    if (i->substr(0, 6) == "--log=") {
      if (logfile_found) {
        std::cerr <<
          "mli: more than one log file given: \"" << logfile_name << "\" and \"" << i->substr(6) << "\"\n"
          << std::endl;
        return EXIT_FAILURE;
      }
      else
        logfile_found = true;

      logfile_name = i->substr(6);
      continue;
    }

    if (i->substr(0, 10) == "--include=") {
      dirs.push_back(i->substr(10));
      continue;
    }

    if (i->substr(0, 12) == "--directive=") {
      std::string str = i->substr(12);
      std::string name("--directive");
      mli::location_type loc;
      loc.initialize(&name);
      int r = mli::directive_read(str, loc);
      if (r != 0)
        return EXIT_FAILURE;
      continue;
    }

    if (infile_found) {
      std::cerr <<
        "mli: more than one input file given: \"" << infile_name << "\" and \"" << *i << "\"\n"
        "Try 'mli --help' for more information."
        << std::endl;
      return EXIT_FAILURE;
    }
    else
      infile_found = true;

    infile_name = *i;
  }

  std::string name_base;

  if (infile_name.size() >= 4 && infile_name.substr(infile_name.size() - 4) == ".mli")
    name_base = infile_name.substr(0, infile_name.size() - 4);
  else
    name_base = infile_name;

  if (infile_name.empty()) {
    std::cerr <<
      "mli: no input file given\n"
      "Try 'mli --help' for more information."
      << std::endl;
    return EXIT_FAILURE;
  }

  if (outfile_name.empty())
    outfile_name = name_base + ".mlo";

  if (logfile_name.empty())
    logfile_name = name_base + ".log";

  if (theory_name.empty())
    theory_name = name_base;

#ifdef DATADIR
  // Convert macro to string: STR(x) expands x, and STR_EXPAND(x) stringifies it.
  #define STR_EXPAND(x) #x
  #define STR(x) STR_EXPAND(x)

  dirs.push_back(STR(DATADIR));
#endif

  if (verbose) {
    std::cout << "Theory: " << theory_name << std::endl;
    std::cout << "Input file: " << infile_name << std::endl;
    std::cout << "Output file: " << outfile_name << std::endl;
    std::cout << "Log file: " << logfile_name << std::endl;

    std::cout << "Directories:";
    for (auto& i: dirs)
      std::cout << " " << i;
    std::cout << std::endl;
  }


  try {
    std::ofstream flog(logfile_name);
    reassign rlog(std::clog, flog);
    mli::theory_database db(theory_name);
    std::ifstream is(infile_name);

    if (!is) {
      std::cerr << "Input file " << infile_name << " not found." << std::endl;
      return EXIT_FAILURE;
    }
		std::cout << "Begin reading " << infile_name << std::endl;

		is >> db;

	  if (!is) {
      std::cerr << "Could not read library " << theory_name << "." << std::endl;
      return EXIT_FAILURE;
    }

    std::ofstream ofs(outfile_name);
    if (!ofs) {
      std::cerr << "Output file " << outfile_name << " not found or accessible." << std::endl;
    }

    ofs << db << std::flush;

	  std::cout << "End reading " << infile_name << std::endl;

	} catch (std::exception& ex) {
	  std::cerr << "Unexpected exception: " << ex.what() << std::endl;
	  return EXIT_FAILURE;
	} catch (...) {
	  std::cerr << "Unexpected exception." << std::endl;
	  return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}

