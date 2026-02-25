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


#include "inferenceengine.hh"

#include "metacondition.hh"
#include "precedence.hh"


namespace mli {

  extern size_type unify_count;


  // Conceptually, the inference tree has the original formula to be proved, or goal,
  // at the root, and then the tree is built with new edges having each a
  // substitutions towards new nodes, each with a new formula, called goal,
  // also to be proved. If one of these formulas are provable, the branch down to the
  // root with constitutes a proof, and they are never put onto the tree. In actuality,
  // all operations start at a leaf: at leaf graft a set of new leaves,
  // the former which becomes and internal node in the process, prune a leaf down
  // to the branching point, or extract a proof by starting at a leaf, moving towards
  // root.
  // So the implementation is currently a foliage data structure, which maintains a
  // list of pointers to the leaves, which in turn have pointers towards the parents,
  // successively leading to the root.


  void inference_tree::write(std::ostream& os, write_style ws) const {
    os << "inference_tree {\n";
    os << "root goal: " << goal_;
#if 0
    // Write nodes_:
    if (root_ != 0) {
      root_->write(os, ws);
    }
#endif
#if 0
    // current_leaf_ has been removed:
    if (current_leaf_ != foliage_.end()) {
      os << std::endl << "Current leaf: ";
      (*current_leaf_)->value_.alternative_.write(os, ws);
    }
#endif
    os << "} inference_tree \n";
  }


  inline std::ostream& operator<<(std::ostream& os, const inference_tree& x) {
    x.write(os, write_default);  return os;
  }


  // The proof tree search inference engine, or evaluator, uses a simple algorithm
  // that allows the partial tree to be built and examined in an arbitrary manner,
  // according to need.
  // If the initial goal at the tree root is already provable, there is nothing to do but
  // registering it as a proof and return. Otherwise construct the tree recursively,
  // starting at the root. The leaf goals are always unprovable:
  // 1. At the currently chosen leaf, call the unifier of the associated goal against
  // the current database (formula sequence of proved formulas, or facts), which produces a
  // set of alternatives, and extract any eventual proofs.
  // (The database can vary with the leaf, like depending on the level.)
  // 2a. If no alternatives remain after the proof extraction, prune the proof tree
  // at the current leaf. If the proof tree becomes empty by that, then the process stops.
  // If there are no proofs registered, then the process failed. Otherwise choose a new
  // leaf according to the style of the engine, and continue at 1.
  // 2b. Otherwise, attach the remaining alternatives to the current leaf,
  // choose a new leaf according to the style of the engine, and continue at 1.
  //
  // The proof tree search algorithm above only stops if the tree becomes empty, which will not
  // occur if the tree is infinite, in which case one stops by some criteria: proof found,
  // or some set limit of a parameter has been reached.
  // The proof tree becomes infinite if for example Modus Ponens (MP) is in the database
  // at all levels.

  proofs prove(const val<formula>& x, database& dbr, size_type n) {
    inference_tree it(x);

    return it.solve(dbr, n);
  }


  long thread_count = -1;


  proofs& inference_tree::solve(database& dbr, size_type n) {
    proofs_found = false;

    long N = thread_count;

    if (thread_count < 0)
      N = (-thread_count)*std::thread::hardware_concurrency();

    if (trace_value & trace_thread)
      std::clog << "Threads: " << N << std::endl;

    // N is now the number of threads to use; none if N == 0.
    if (N == 0)
      evaluate(dbr, n);
    else {
      std::vector<std::thread> threads;

      // Create up to N threads with the select-solve_one loop, as long as the
      // tree is not empty, and the required proofs have not been found:
      for (int k = 0; k < N && !proofs_found && !empty(); ++k)
        // Lambda wrap for 'evaluate' select-solve_one loop passed to std::thread:
        threads.push_back(std::thread([this, &dbr, n] { evaluate(dbr, n); }));

      if ((trace_value & trace_thread) && threads.size() < N)
        std::clog << "Used threads: " << threads.size() << "/" << N << std::endl;

      // Joining threads.
      for (auto& i: threads)
        i.join();
    }

    // Report result of proof search.
    if (trace_value & trace_result) {
      if (proofs_.empty())
        std::clog << "Proof failed.\n" << std::flush;
      else
        std::clog << "Proof succeeded.\n" << std::flush;
    }

    // Reset variable for subsequent solve().
    proofs_found = false;

    return proofs_;
  }


} // namespace mli

