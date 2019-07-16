# features / todo list
* main solver
  - [X] conflict-driven clause-learning
  - [X] VSIDS branching heuristic
  - [ ] polarity-saving
  - [ ] on-the-fly hyper-binary-resolution
  - [ ] clause-cleaning heuristic
  - [ ] on-the-fly minimization of learnt clauses
* preprocessing / inprocessing
  - [ ] subsumption / self-subsuming resolution
  - [x] strongly-connected-components
  - [ ] bounded variable elimination
  - [ ] bounded variable addition (at least some?)
  - [ ] xor discovery and gaussian elimination
* data-structures
  - [x] two-watch scheme
  - [x] implicit binary clauses
  - [ ] implicit ternary clauses (and blocking literal)
  - [x] packed long clauses with 32-bit references
  - [ ] small-vector optimization for binaries and watches
* other
  - [ ] unsat proofs
  - [ ] multithreading
  - [ ] memory-efficient reading of huge problems
