Vector Valued Eisenstein Series
===============================

Implementation of several algorithms for the computation (with sage) of vector valued Eisenstein series for the Weil representation w.r.t. an even lattice or a finite quadratic module.
The algorithms are part of (and were written in the course of) the authors PhD thesis at the Technische Universität Darmstadt.
Version 1 is archived under https://zenodo.org/badge/latestdoi/153112288.


Installation
============

-  A) On your own computer which has sage (we recommend version 8.1) and git installed (see dependencies below):

   Go to the directory where you would like to download the repository to.

   You should be able to simply run:
   ```
    $ git clone https://github.com/s-opitz/eisenstein_series.git
   ```
   You can now use the code by starting sage from this directory.

-  B) Use the code in CoCalc, (https://cocalc.com):
 
   This is a nice possibility to try out the programs
   if you don't have sage installed.

   Load the file integer_lattice.py into a project. 
   Start a sage worksheet and proceed as in the tutorial.
   This is enough to try out the most important algorithms.
   If the other files are needed, also load them into the project.

Tutorial
========

   To start computing vector valued Eisenstein series, run the following command from the directory containing the file integer_lattice.py:

   ```
   sage: from eisenstein import EisensteinSeries

   # The classical Eisenstein series of weight 4:
   sage: EisensteinSeries('', 4)

   A vector valued q-series with coefficients
   (): 1 q^(0) + 240 q^(1) + 2160 q^(2) + O(q^(3))

   # These Fourier coefficients were tested with the Siegel-Weil formula:
   sage: EisensteinSeries(matrix(2,2,[2,1,1,2]), weight = 5)

   A vector valued q-series with coefficients
   (0, 0): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
   (1/3, 1/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
   (2/3, 2/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))

   # Using the negative Gram matrix and the dual Weil representation gives the same result:
   sage: EisensteinSeries(- matrix(2,2,[2,1,1,2]), weight = 5, dual = True)

   A vector valued q-series with coefficients
   (0, 0): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
   (1/3, 1/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
   (2/3, 2/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))

   # We can also compute the Eisenstein series from a genus symbol:
   sage: EisensteinSeries('3^-1', 5)

   A vector valued q-series with coefficients
   ((3, (0, 0, 0, 0)),): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
   ((3, (0, 0, 0, 1/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
   ((3, (0, 0, 0, 2/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))

   # Using the genus symbol for the finite quadratic module twisted with -1
   # and the dual Weil representation gives the same result:
   sage: EisensteinSeries('3^1', 5, dual = True)

   A vector valued q-series with coefficients
   ((3, (0, 0, 0, 0)),): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
   ((3, (0, 0, 0, 1/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
   ((3, (0, 0, 0, 2/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
   ```
   
   The Lattice class can do more than just compute Eisestein series, for a start try out the following:
   ```
   sage: from integer_lattice import Lattice, A, E, H, U
   ```

   You might like to try the following command for a short introduction:
   ```
   sage: Lattice?
   ```

   Initializing a lattice by a Gram matrix:
   ```
   sage: L = Lattice(matrix(2,2,[0,1,1,0]))
   sage: L.gram_matrix()
   [0 1]
   [1 0]
   ```

   Initializing a lattice by the coefficients of its quadratic form:
   ```
   sage: L = Lattice(ZZ, 2, [1,1,1])
   sage: L.gram_matrix()
   [2 1]
   [1 2]
   ```

   For information on the provided functions, you might want to try commands with '?' attached:
   ```
   sage: L.eisenstein_series?
   ```

   Some of the root lattices (H and U above give hyperbolic planes):
   ```
   sage: A(1)

   Lattice given by "Ambient free module of rank 1 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 1 variables over Integer Ring with coefficients: 
   [ 1 ]"

   sage: A(2)

   Lattice given by "Ambient free module of rank 2 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 2 variables over Integer Ring with coefficients: 
   [ 1 -1 ]
   [ * 1 ]"

   sage: A(3)

   Lattice given by "Ambient free module of rank 3 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 3 variables over Integer Ring with coefficients: 
   [ 1 -1 0 ]
   [ * 1 -1 ]
   [ * * 1 ]"

   sage: E(6)

   Lattice given by "Ambient free module of rank 6 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 6 variables over Integer Ring with coefficients: 
   [ 1 -1 0 0 0 0 ]
   [ * 1 -1 0 0 0 ]
   [ * * 1 -1 0 -1 ]
   [ * * * 1 -1 0 ]
   [ * * * * 1 0 ]
   [ * * * * * 1 ]"

   sage: E(7)

   Lattice given by "Ambient free module of rank 7 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 7 variables over Integer Ring with coefficients: 
   [ 1 -1 0 0 0 0 0 ]
   [ * 1 -1 0 0 0 0 ]
   [ * * 1 -1 0 0 0 ]
   [ * * * 1 -1 0 -1 ]
   [ * * * * 1 -1 0 ]
   [ * * * * * 1 0 ]
   [ * * * * * * 1 ]"

   sage: E(8)

   Lattice given by "Ambient free module of rank 8 over the principal ideal domain Integer Ring" endowed with the quadratic form "Quadratic form in 8 variables over Integer Ring with coefficients: 
   [ 2 -2 0 0 0 0 0 1 ]
   [ * 1 -1 0 0 0 0 0 ]
   [ * * 1 -1 0 0 0 0 ]
   [ * * * 1 -1 0 0 0 ]
   [ * * * * 1 -1 0 0 ]
   [ * * * * * 1 -1 0 ]
   [ * * * * * * 1 0 ]
   [ * * * * * * * 1 ]"
   ```

   Adding and scaling lattices:
   ```
   sage: L = H()
   sage: L = 2*H() + H(2)
   sage: L.gram_matrix()

   [0 1 0 0 0 0]
   [1 0 0 0 0 0]
   [0 0 0 1 0 0]
   [0 0 1 0 0 0]
   [0 0 0 0 0 2]
   [0 0 0 0 2 0]
   ```

   Recovering the classical Eisenstein series:
   ```
   sage: L = Lattice(matrix(2,2,[0,1,1,0]))
   sage: L.eisenstein_series(4, prec = 10)
   {(0, 0): {0: 1,
     1: 240,
     2: 2160,
     3: 6720,
     4: 17520,
     5: 30240,
     6: 60480,
     7: 82560,
     8: 140400,
     9: 181680}}
   sage: EisensteinSeries(_)

   A vector valued q-series with coefficients
   (0, 0): 1 q^(0) + 240 q^(1) + 2160 q^(2) + 6720 q^(3) + 17520 q^(4) + 30240 q^(5) + 60480 q^(6) + 82560 q^(7) + 140400 q^(8) + 181680 q^(9) + O(q^(10))

   sage: L.eisenstein_series(6, prec = 10)
   {(0, 0): {0: 1,
     1: -504,
     2: -16632,
     3: -122976,
     4: -532728,
     5: -1575504,
     6: -4058208,
     7: -8471232,
     8: -17047800,
     9: -29883672}}
   sage: EisensteinSeries(_)

   A vector valued q-series with coefficients
   (0, 0): 1 q^(0) + -504 q^(1) + -16632 q^(2) + -122976 q^(3) + -532728 q^(4) + -1575504 q^(5) + -4058208 q^(6) + -8471232 q^(7) + -17047800 q^(8) + -29883672 q^(9) + O(q^(10))
   ```

   Computing isometry orbits for the discriminant group of L:
   ```
   sage: L = Lattice(ZZ,2,[1,1,1])
   sage: L.gram_matrix()
   [2 1]
   [1 2]
   sage: L.isometry_orbits()
   [[(0, 0)], [(1/3, 1/3), (2/3, 2/3)]]
   ```

   Computing the coefficients just once for each orbit above:
   ```
   sage: L.eisenstein_series_by_orbits(5,prec = 10)
   {0: {0: 1,
     1: 246,
     2: 3600,
     3: 19686,
     4: 59286,
     5: 149760,
     6: 295200,
     7: 590892,
     8: 925200,
     9: 1594326},
    1: {1/3: 3,
     4/3: 723,
     7/3: 7206,
     10/3: 28080,
     13/3: 85686,
     16/3: 185043,
     19/3: 390966,
     22/3: 658800,
     25/3: 1170003,
     28/3: 1736646}}
   ```
   Testing via the Siegel-Weil formula:
   ```
   sage: L2 = (L + E(8))
   sage: L2.theta_series_symmetrized(prec = 3)
   {(0, 0, 0, 0, 0, 0, 0, 0, 0, 0): {0: 1, 1: 246, 2: 3600},
    (1/3, 1/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206},
    (2/3, 2/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206}}
   sage: L2.eisenstein_series(5,prec = 3)
   {(0, 0, 0, 0, 0, 0, 0, 0, 0, 0): {0: 1, 1: 246, 2: 3600},
    (1/3, 1/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206},
    (2/3, 2/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206}}
   ```

   Computing Eisenstein series for a finite quadratic module:
   ```
   sage: from finite_quadratic_module import FiniteQuadraticModule
   sage: from local_data_to_eisenstein_series import LocalSpaceByJordanData
   sage: F = FiniteQuadraticModule(matrix(2,2,[0,1,1,0]))
   sage: J = F.jordan_decomposition()
   sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
   sage: el = L.discriminant_form_iterator().next()
   sage: el.eisenstein_series(4, prec = 10)

   {0: 1,
    1: 240,
    2: 2160,
    3: 6720,
    4: 17520,
    5: 30240,
    6: 60480,
    7: 82560,
    8: 140400,
    9: 181680}
   ```


Dependencies
============

   - sage: A current version of sage
   - finite_quadratic_module from psage (N.-P. Skoruppa et. al.)
     (This is necessary if the Eisenstein series is computed with respect to a finite quadratic module, you need to use the version included here, where it is possible to extract the data of the genus symbol.)
     Some functions in this module produce errors when using version 8.3 of sage. It is due to this, that we cannot currently support sage version 8.3 (completely) and hence recommend to use version 8.1.
   - genus_symbol from sfqm (S. Ehlen)

ToDo
====

   - Integrate the local algorithms into the genus symbol class (S.Ehlen) and remove the dependency on psage.
   - Make the code completely compatible with sage version 8.3.
   


