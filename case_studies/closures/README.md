# Closures

This subdirectory contains various versions of weak normalization for a closure-based
presentation of the linear λ-calculus.
The encoding is based on standard de Bruijn notation (not well-scoped).
The operational semantics is big-step and does not perform substitutions, so no shifting nor substitution lemmas are required.

## Files

- **ndbclo.v**:  
  Numbered (but not well-scoped) DB encoding. 
  Includes proofs of subject reduction and weak normalization.

- **basicIclo.v**:  
  Intrinsically-typed DB version, but **not** linear. 
  Meant as a stepping stone toward a future fully linear version.