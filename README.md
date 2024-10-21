# MIRS
MAGMA package for computing maximal irreducible solvable subgroups of GL(n,q).

The code is based on results in [_Maximal Solvable Subgroups of Finite Classical Groups_](https://doi.org/10.1007/978-3-031-62915-0) (Lecture Notes in Mathematics, vol. 2346, Springer, 2024), where one of the main results is the classification of maximal irreducible solvable subgroups of GL(n,q).

The intrinsic ```MIRSGL``` in the package is implemented only for certain values of n, but for arbitrary q.

Currently implemented values:
  ```
  n = 2^a * 3^b * 5^c * 7^d * 11^e * ..., where:
    0 <= a <= 6
    0 <= b <= 4
    0 <= c <= 3
    0 <= d,e <= 2
    for all other primes, exponent <= 1.
  ```

In particular, this works for all ```1 <= n <= 127```. Also works for all squarefree ```n```.

# Files and usage

Information on working with MAGMA spec files and packages can be found here: [http://magma.maths.usyd.edu.au/magma/handbook/text/24](http://magma.maths.usyd.edu.au/magma/handbook/text/24).

The package contains the following files:

```
MIRS.spec
GSp_data.m
GSp_gens.m
MIRS.m
```

Place all of these files in the same folder. Then to load the package in MAGMA, use the command ```AttachSpec``` to load the package. 

For example, if ```MIRS.spec``` is in the current working directory, the command

```
AttachSpec("MIRS.spec");
```

loads the package.

# Example

```
// Maximal irreducible solvable subgroups of GL(12,5).
L := MIRSGL(12,5);

// Primitive maximal irreducible solvable subgroups of GL(12,5).
K := MIRSGL(12,5 : PRIMITIVE_ONLY := true);
```
