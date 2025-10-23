# Closures

This dir contains various versions of weak normalization for a closure
based presentation of the linear lambda calculus: the encoding is based on
standard DB notation -- not well scoped. The op sem is big step and
does not perform substitutions, hence no shifting is required nor any
substitution lemma.

They all use Hammer, so _not_ compatibile with current Rocq

- ndbclo.v: numbered (but not well scoped) DB: subject reduction and WN

- basicIclo.v:  intrinsically typed DB version, but **not** linear --- meant as a stepping stone to a linear one.

