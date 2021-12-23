The Coq code depends on the UniMath library, available from
http://github.com/UniMath/UniMath.

Functions f : a → b and g : c → d are weakly orthogonal if for any
commutative square there is a diagonal h : b → c making the diagram
commute:
```
        i
     a  →  c
        h
   f ↓  ↗  ↓ g

     b  →  d
        j
```
It is said that f has the left lifting property with respect to g, and
g has the right lifting property with respect to f.

Examples of lifting properties formalized in this repository:
- surjections have right lifting property with respect to the simplest
  non-surjective function ∅ → unit,
- inclusions have right lifting property with respect to the simplest
  non-inclusion bool → unit.

See more details and examples here:
https://ncatlab.org/nlab/show/lift.

