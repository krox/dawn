# features / todo list / ideas
* main solver
  * clause learning
    - [x] UIP style
    - [ ] full resolution to one variable per level
    - [x] on-the-fly minimization of learnt clauses
    - [x] lazy hyper-binary-resolution
  * branching heuristic
    - [x] VSIDS
    - [x] polarity-saving
  * clause-cleaning heuristic
    - [x] size
    - [x] glue
    - [ ] activity
* preprocessing / inprocessing
  - [x] subsumption / self-subsuming resolution
  - [x] transitive reduction of binary clauses
  - [ ] disconnected components
  - [x] strongly-connected-components
  - [ ] bounded variable elimination
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
