# features / todo list / ideas
* main solver
  * clause learning
    - [x] UIP style
    - ~~[x] full resolution to one variable per level (default=off)~~
    - [x] on-the-fly minimization of learnt clauses
    -  ~~lazy hyper-binary-resolution~~
  * branching heuristic
    - [x] VSIDS
    - [x] polarity saving
    - [x] dominating-literal branching (default=off)
  * clause-cleaning heuristic
    - [x] size
    - ~~glue (computed once when learning)~~
    - [ ] glue (dynamicically adjusted during propagation)
    - [ ] activity
  * restart heuristic
    - [x] linear
    - [ ] geometric
    - [ ] luby
    - [ ] dynamic
* preprocessing / inprocessing
  - [x] top-level in-tree probing (including hyper-binary resolution)
  - [x] subsumption / self-subsuming resolution (includes HTE)
  - [x] vivification (more exhaustive than typical heuristics)
  - [x] transitive reduction of binary clauses
  - [ ] disconnected components
  - [x] strongly-connected-components
  - [x] blocked-clause elimination
  - [x] bounded variable elimination (preprocessing only)
  - [x] bounded variable addition (default=off)
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
