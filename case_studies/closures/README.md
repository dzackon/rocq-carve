# Closures

This dir contains various versions of weak normalization for linear closures. 
They all use Hammer, so _not_ compatibile with current Rocq

- ndbclo.v: numbered (but not well scoped) DB: subject reduction an WN

- selfclo.v: the same as above but **not** relying on CARVe. Everything needed is there from scratch. Useful to experiment 

- basicIclo.v:  intrinsically typed DB version, but **not** linear --- meant as a stepping stone to a linear one.

- Idbclo.v: the porting in progress of `basicIclo` to the _linear_ case. Very much in progress