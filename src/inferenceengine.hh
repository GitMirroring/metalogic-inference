/* Copyright (C) 2017, 2021-2023 Hans Åberg.

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

#pragma once


#include <list>
#include <tuple>

#include <queue>

#include <thread>
#include <mutex>


#include "MLI.hh"
#include "substitution.hh"


#define NEW_THREAD 1
#define NEW_TREE_MUTEX 1


namespace mli {

  /* Calculation of proofs:

  The inference-engine maintains an inference-tree with edges an alternative,
  a pair (s, g) where s is a substitution, and g is a goal (formula) that
  must be proved for the completetion of the proof. Each path from the root
  in the inference-tree corresponds to a proof-line. The proof-line is 
  successful if the last edge has an empty (trivially true) goal. The proof
  line is a failure if an end-goal cannot be extended with a new edge. The
  inference-tree can be extended by choosing an arbitrary end-edge, and see
  if the end-goal can, via unification, produce a list of new alternatives,
  which then can be inserted as edges into the inference-tree. Currently,
  a breadth-frist search is used; one point is that if there is a finite proof,
  it will always be found.
  */


  extern size_type unify_count;


  class inference_tree {
  public:
    class node;

    using leaf = node*;
    using leaf_container = std::list<leaf>;
    using iterator = leaf_container::iterator;

    typedef long unsigned size_type;
    typedef size_type weight;

    struct value {
      alternative alternative_;   // Node data.
      size_type weight_ = 0;      // Node weight.

      value() = default;
      value(const alternative& a, weight w) : alternative_(a), weight_(w) {}
    };

    // The tree iterator must be able to conveniently access the parent and the
    // next sibling, so the parent reference need to be of the same type as
    // of the siblings and the each of the children. As the last use a list
    // iterator, the parent pointer becomes the same. An alternative would
    // be using node* for all, and implement the tree structure from scratch.
    class node {
    public:
      node* parent_ = nullptr;
      size_type size_ = 0;
      size_type level_ = 1;

      size_type count_ = 0; // For keeping sorting order.

      value value_;

      node() = default;
      ~node() { if (parent_ != nullptr) --parent_->size_; }

      node(const alternative& a, node* p = nullptr, weight w = 0, size_type k = 0)
       : value_(a, w), parent_(p), level_(p? p->level_ + 1 : 1), count_(k) {
        if (p != nullptr) ++p->size_;
      }

      bool leaf() const { return size_ == 0; }

      void write(std::ostream& os, write_style ws) const {
        os << "node{\n";
#if 0
        bool iter0;
        for (auto& i: nodes_)
          if (iter0) iter0 = false;
          else {
            os << "\n";
            i.write(os, ws);
          }
#endif
        os << "\n} node\n";
      }
    };



    // As the unifier produces alternatives containing both goal, substitution,
    // as well as other information, such as for displaying the proof, each
    // alternative is put on a separate node, as leaves through the 'graft' function.
    // The leaves then hold the goals to be proved.
    // The root just holds the initial goal in the form of a default alternative.

    ref<formula> goal_;         // Initial goal to be proved.

    // Proof extracted so far from the proof tree search; proofs are never on the tree itself.
    proofs proofs_;

    // Set to true when the required proofs have been found, terminating further search.
    bool proofs_found = false;


    struct priority {
      // The operator()(x,y) functions as the order x < y for the priority queue
      // which outputs the largest element first. Thus, if operator()(x,y) returns
      // true, then y is output before x.
      // Thus, to get the smallest weight, the order should be reversed, giving the
      // value weight(x) > weight(y).
      // For equal weights, using count(x) output earlier/later alternatives first:
      //   count(x) > count(y) outputs earlier alternatives first
      //   count(x) < count(y) outputs later alternatives first
      bool operator()(leaf x, leaf y) {
        if (x->value_.weight_ != y->value_.weight_)
          return x->value_.weight_ > y->value_.weight_;

        // count(x) < count(y) outputs later alternatives first:
        return x->count_ < y->count_;
      }
    };


    // For sorting relative the creation order of the alternatives.
    size_type node_count_ = 0;

    std::priority_queue<leaf, std::vector<leaf>, priority> queue_;


    // Mutual exclusion thread locks, to prevent simultaneous modification of the tree:
    // The tree_mutex_ makes sure that the operations 'select', 'graft' and 'prune'
    // do not conflict, also when calling 'empty', which is set by 'prune' and checked by
    // 'select'.
    // The proofs_mutex_ makes sure add to proofs container proofs_ in get_proof of
    // different threads do not conflict.
    std::mutex proofs_mutex_, tree_mutex_;

    // Notify 'select' from 'graft' that the queue holds an element, and 'prune' that the tree is empty:
    std::condition_variable select_cond_;

    // Notify from 'prune' that the resulting tree is empty, so that the proof search has finished.
    bool tree_empty_ = true;


    inference_tree() = default;

    // The destructor only destroys leaves in the the leaf container queue_; the
    // leaves in the threads are destroyed by calling 'prune'.
    ~inference_tree() {
      // Delete tree by successively pruning all leaves.
      // As the inference_tree object in 'prove' is destroyed after the threads in
      // 'solve' have stopped, mutex locks are not required here.

#if NEW_THREAD
      while(!queue_.empty()) {
        leaf np = queue_.top();
        queue_.pop();

        prune(np);
      }
#else
      while(!queue_.empty()) {
        prune(queue_.top());

        // Lock thread tree_mutex_, to make sure 'graft' or 'select' in some other
        // thread does not conflict.
        std::lock_guard<std::mutex> guard(tree_mutex_);

        queue_.pop();
      }
#endif
    }


    // The root is initially a single leaf. If all leaves are pruned, also the initial
    // leaf is deleted, preventing it to be re-examined. If the same instance of
    // inference_tree is to be re-used, a new root formula would have to be added.
    inference_tree(const ref<formula>& x)
     : goal_(x), tree_empty_(false)
    {
      // Boolean cases:
      // A consistent tree has no leaves with provable (true) formulas, so these
      // must be excluded from a proof search, leaving the tree empty. Cases:
      // true   Initial goal provable; register it as a proof, leaving the tree empty.
      // false  Move onto proof search, doing nothing here.
      if (x->provable()) {
        // Initial goal is already provable, so in order to keep the tree consistent,
        // with no provable leaves, register it as a proof and leave the tree empty.
        tree_empty_ = true;
        proofs_found = true;
        proof pf(x);
        pf.push_back(alternative(ref<substitution>(make), x));
        proofs_.push_back(pf);
        return;
      }

      queue_.push(new node(alternative(ref<substitution>(make), x)));
    }


    // The inference tree is empty when all leaves have been removed, both in the
    // leaf queue, and those in each active thread, which occurs when a 'prune'
    // reaches the root, that is a nullptr node. When this occurs, 'select' is
    // notified so that it can wake and return nullptr.
    bool empty() const noexcept { return tree_empty_; }


    // Assumption: np != nullptr.
    proof get_proof(leaf np) {
      proof pf(goal_);

      // In this extraction, the root is excluded, which just holds the
      // original formula goal, as it is added separately above.
      for (; np->parent_ != nullptr; np = np->parent_)
        pf.push_front(np->value_.alternative_);

      return pf;
    }


    // Extract proof completions at the leaf i from as.
    // The return is the number of proofs found in this call.
    // After this call, if what remains from as is non-empty, it should
    // be grafted onto the tree, otherwise, the leaf i should be pruned.
    size_type get_proof(alternatives& as, leaf i, size_type n) {

      size_type k = 0;  // Increased for each proof found.

      for (auto j = as.begin(); j != as.end();) {
        // Boolean cases:
        // true     Register proof at j and then erase j from alternatives.
        // false    Move onto next iterator j, keeping alternatives intact (doing nothing).
        if (j->goal_->provable()) {
          // Other threads may have found required proofs while this thread
          // being locked, so in that case, skip this proof:
          if (proofs_found)
            throw thread_exit();

          // Set to proof base if proof is found.
          proof pf = get_proof(i);

          // Add last alternative of proof:
          pf.push_back(*j);

          // Set the proof to conditional if not all statements used have a strict proof:
          pf.set_conditional();

          {
            // Lock thread mutex while proof container is modified:
            std::lock_guard<std::mutex> guard(proofs_mutex_);

            proofs_.push_back(pf);
          }
          ++k;

          j = as.erase(j);

          // Writes proofs as they occur:
          if (trace_value & trace_proof) {
            std::lock_guard<std::recursive_mutex> guard(write_mutex);
            std::clog << "\n";
            pf.write(std::clog, write_default);
          }

          // Continue proof search when condition P(n) is true, where
          //   P(n) ≔ n = 0 or less than n proofs found.
          // Thus, the search ends when n > 0 and if at least n proofs have been found.
          if (n == 0 || proofs_.size() < n)
            continue;

          // Required proofs found, so cause other threads to cease unify, and stop here:
          proofs_found = true;
          select_cond_.notify_all();
          throw thread_exit();
        }
        else
          ++j;
      }

      return k;
    }


    // At the leaf i, unify its goal against the database dbr as fact; extract eventual proofs;
    // if alternatives remain, graft them, otherwise prune i. The first return is
    // the number of proofs found in this solve.
    // The second return value is true if a graft was done, otherwise it was a prune:
    // A graft or a prune is always performed, in order to leave the tree in a
    // consistent state.
    std::tuple<size_type, bool> solve_one(leaf i, database& dbr, size_type n) {

      // Renaming of formulas take place in each database::unify(). The degree number is
      // used to distinguish variables of different unification statement instantiations.
      // Set to 0 before the top level invocation of mli::unify and incremented during
      // subsequent unification calls when alternatives are produced.

      degree_pool sl;  // For finding smallest unused definition degree number.
      unify_count = 0;  // Start to count unify() calls for this unification iteration.
      ref<formula> f = get_goal(i);
      size_type lv = get_level(i);

      // A reference to the pertinent level part of the database is passed on here, so that in the
      // unificiation the level value is only used for variable renamning, and not for database selection.
      // The sublevel is though used for that, and cannot be moved here, as it has to be done during the
      // formula sequence metaand (goal) unification.

      alternatives as = mli::unify(f, {goal, f->metalevel()}, &dbr[lv], {fact, 0_ml}, &dbr[lv], lv, sl);

      if (trace_value & trace_solve) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog
          << "Solve, level " << get_level(i) << "/" << i->value_.weight_ << ":" << queue_.size()
          << ", find(\n  " << get_goal(i) << "):\n{size " << as.size() << ": " << as << "\n}" << std::endl;
      }

      // The proof line from the root up to the current edge is passed to the solutions
      // function, which in turn works through all alternatives just found to find proof
      // completions, the rest being the return that is pushed onto the tree.

      size_type k = get_proof(as, i, n);

      // Cause a 'prune' on the leaf i by clearing 'as'.
      if (proofs_found)
        as.clear();

      if (as.empty()) {
        // As there are no alternatives to attach to the tree, instead
        // prune the tree at the current edge and relocate to a new leaf.

        if (trace_value & trace_solve) {
          std::lock_guard<std::recursive_mutex> guard(write_mutex);
          std::clog << "Level " << get_level(i) << " prune: " << std::endl;
        }

        if (trace_value & trace_prooftree)
          std::clog << "Tree before prune: " << *this << std::endl;

        // Faster to not do selection on prune:
        prune(i);

        if (trace_value & trace_prooftree)
          std::clog << "Tree after prune: " << *this << std::endl;

        return std::tuple(k, false);
      }

      if (level_max > 0 && get_level(i) >= level_max)
        throw interpret_error("Exceeding set max inference tree level.");

      if (trace_value & trace_solve) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "Level " << get_level(i) << " graft: " << std::endl;
      }

      if (trace_value & trace_prooftree)
        std::clog << "Tree before graft: " << *this << std::endl;

      // Graft alternatives onto inference tree at the current leaf.
      // Then continue at a new leaf, according to the engine style.
      // Currently, both operations are in the 'graft' function.
      graft(i, as);

      if (trace_value & trace_prooftree)
        std::clog << "Tree after graft: " << *this << std::endl;

      return std::tuple(k, true);
    }


    // The evaluator, recursively picking a leaf and solve it, until a termination
    // condition occurs: the tree is empty or required proofs found.
    bool evaluate(database& dbr, size_type n) {
      leaf i = nullptr;

      // A thread_exit exception thrown, as in 'unify', terminates the evaluation loop:
      try {
        for (;;) {
          // Prove goal (formula) at the current proof tree leaf (end node):

          // First call 'select' to get a leaf and a formula to prove. After that, call
          // 'solve' of this leaf which calls 'unify' to get a list of alternatives, from
          // which any eventual proof completions are extracted. If alternatives remain,
          // they are grafted onto the leaf i, which becomes an internal node. Otherwise,
          // with no alternatives, it is a dead branch, which is pruned down to the branching
          // point on the tree. In both cases, the current formula via its proof line cannot
          // be reached again, ensuring that no formula via its proof line is investigated more
          // than once.

          i = select();

          // 'select' returns nullptr if tree is empty or required proofs found, ending the loop:
          if (i == nullptr)
            return true;

          if (trace_value & trace_solve) {
            std::lock_guard<std::recursive_mutex> guard(write_mutex);
            std::clog << "Solve " << get_level(i) << "/" << i->value_.weight_ << ":" << queue_.size() << "\n"
              << "Substitution: " << get_alternative(i).substitution_ << "\n"
              << "Goal: " << get_goal(i) << std::endl;
          }
          else if (trace_value & trace_level) {
            // Overridden by trace_solve since first line is the same.
            std::lock_guard<std::recursive_mutex> guard(write_mutex);
            std::clog << "Solve " << get_level(i) << "/" << i->value_.weight_ << ":" << queue_.size() << std::endl;
          }

          inference_tree::solve_one(i, dbr, n);
        } // for (;;)
      }
      catch (thread_exit&) {
        // When thread_exit is thrown, the leaf has not been pruned, which is done here
        // in order to avoid a memory leak:
        prune(i);
      }

      return false;
    }


    // Sets up threads and required data around evaluate.
    proofs& solve(database& dbr, size_type n);


    alternative get_alternative(leaf i) {
      if (i == nullptr)
        return alternative();
      return i->value_.alternative_;
    }


    ref<formula> get_goal(leaf i) {
      if (i == nullptr)
        return goal_;
      return i->value_.alternative_.goal_;
    }


    // Insert alternatives 'as' as new leaves at leaf i, which by the process, if 'as'
    // is non-empty, will becomes an internal node, and not a leaf. The return is
    // true if a graft was done, otherwise false.
    bool graft(leaf np, const alternatives& as) {
      if (as.empty())
        return false;

      // Lock queue thread mutex: Though the graft is independent of a prune at any other leaf,
      // strictly, only the queue_ needs be locked, not 'prune', and then provide
      // a way in 'select' to wait for two different locks, though a single mutex
      // is used here for simplicity.
#if NEW_THREAD
      std::unique_lock<std::mutex> lock(tree_mutex_);
#else
      std::lock_guard<std::mutex> guard(tree_mutex_);
#endif

      size_type n = as.size();
      weight w = np->value_.weight_;
      size_type l = np->level_;

      for (auto& a: as) {
        size_type m = a.goal_->metasize();

        node* n1p = new node(a, np, w + m, ++node_count_);
        queue_.push(n1p);
      }

#if NEW_THREAD
      // Unlock before notifying, to avoid waking up a thread that is immediately blocked.
      lock.unlock();
#endif

      // After all leaf queue modifications being done, notify one thread waiting 'select'
      // that the queue is non-empty, which in turn notifies the 'select' waiting in
      // other threads if the leaf queue remains nonempty after the selection:
      select_cond_.notify_one();

      return true;
    }


    // Select a new leaf, the details are handled by the leaf queue and its type:
    // The priority queue may use factors such as the weight of the leaf.
    leaf select() {

      // Lock thread mutex while queue is modified:
      std::unique_lock<std::mutex> lock(tree_mutex_);

      // Wait for notification from 'prune' or 'graft'. If from 'graft', then
      // the leaf queue is nonempty; if from 'prune', then the whole tree is empty:
      select_cond_.wait(lock, [this]{ return !queue_.empty() || empty() || proofs_found; });

      // If the tree is empty, also no leaves in the threads, there is nothing to wait for,
      // the proof search being finished. Since the tree_mutex_ is locked, the value
      // cannot be changed by a 'prune' before the 'wait' call.
      if (empty() || proofs_found)
        return nullptr;

      leaf np = queue_.top();

      queue_.pop();

#if NEW_THREAD
      // Unlock before notifying, to avoid waking up a thread that is immediately blocked.
      lock.unlock();
      select_cond_.notify_one();
#else
      // If queue remains nonempty, notify 'select' in one other thread.
      if (!queue_.empty())
        select_cond_.notify_one();
#endif

      return np;
    }


    // Delete this proof line branch, i.e., singleton nodes, from the leaf
    // towards the root until a branching point. The return value is true if a prune
    // took place, otherwise it is false.
    bool prune(leaf np) {

      // Lock thread mutex while tree is modified:
      // Since the node deletion affects node::size_, which in turn determines whether
      // further nodes are to be deleted, the mutex is locked until the whole branch
      // down to the branching point is deleted.
      // Also, this also locks the 'graft' threads, because C++ does not provide a way
      // in 'select' to wait for two different locks.
      std::lock_guard<std::mutex> guard(tree_mutex_);

      while (np != nullptr && np->leaf()) {
        node* pp = np->parent_;
        delete np;
        np = pp;    // Move one step towards the root.
      }

      if (np == nullptr) {
        tree_empty_ = true;
        // All thread waiting 'select' should now be terminated:
        select_cond_.notify_all();
      }

      return true;
    }


    // The level is the distance from the root plus one, with the latter
    // having level 1. The empty tree, or a nullptr is set to level 0.
    size_type get_level(leaf np) const {
      return np? np->level_ : 0;
    }

    void write(std::ostream&, write_style) const;

    friend std::ostream& operator<<(std::ostream& os, const inference_tree& x);
  };


} // namespace mli

