# features / todo list / ideas
* main solver
  * clause learning
    - [x] UIP style
    - [x] full resolution to one variable per level (default=off)
    - [x] on-the-fly minimization of learnt clauses
    - [x] lazy hyper-binary-resolution
  * branching heuristic
    - [x] VSIDS
    - [x] polarity saving
    - [x] dominating-literal branching (default=off)
  * clause-cleaning heuristic
    - [x] size
    - [x] glue (computed once when learning)
    - [ ] glue (dynamicically adjusted during propagation)
    - [ ] activity
  * restart heuristic
    - [x] linear
    - [ ] geometric
    - [ ] luby
    - [ ] dynamic
* preprocessing / inprocessing
  - [x] subsumption / self-subsuming resolution (includes HTE)
  - [x] vivification (default=off)
  - [x] transitive reduction of binary clauses
  - [ ] disconnected components
  - [x] strongly-connected-components
  - [ ] blocked-clause elimination
  - [x] bounded variable elimination (preprocessing only)
  - [ ] bounded variable addition (at least some?)
  - [ ] xor discovery and gaussian elimination
* data-structures
  - [x] two-watch scheme
  - [x] implicit binary clauses
  - [ ] implicit ternary clauses (and blocking literal)
  - [x] packed long clauses with 32-bit references
  - [x] small-vector optimization for binaries and watches
* other
  - [ ] unsat proofs
  - [ ] multithreading
  - [ ] interface for incremental problems
