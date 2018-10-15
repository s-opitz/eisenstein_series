## This is a python library to be used with sage for the computation of vector valued Eisenstein series for the Weil representation w.r.t. an even lattice.
##*****************************************************************************
##       Copyright (C) 2018 Sebastian Opitz
##
##
##    This program is free software: you can redistribute it and/or modify
##    it under the terms of the GNU General Public License as published by
##    the Free Software Foundation, either version 3 of the License, or
##    (at your option) any later version.
##
##    This program is distributed in the hope that it will be useful,
##    but WITHOUT ANY WARRANTY; without even the implied warranty of
##    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##    GNU General Public License for more details.
##
##    You should have received a copy of the GNU General Public License
##    along with this program.  If not, see <https://www.gnu.org/licenses/>.
##
##*****************************************************************************

## To start computing vector valued Eisenstein series, run the following command from the directory containing the file integer_lattice.py:

sage: from integer_lattice import Lattice, A, E, H, U

## You might like to try the following commands for a short introduction:

sage: Lattice?

## Initializing a lattice by a Gram matrix:

sage: L = Lattice(matrix(2,2,[0,1,1,0]))
sage: L.gram_matrix()

[0 1]
[1 0]

## Initializing a lattice by the coefficients of its quadratic form:

sage: L = Lattice(ZZ, 2, [1,1,1])
sage: L.gram_matrix()

[2 1]
[1 2]

## For information on the provided functions, you might want to try commands with '?' attached:

sage: L.eisenstein_series?

## Some of the root lattices (H and U above give hyperbolic planes):

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

## Adding and scaling lattices:

sage: L = H()
sage: L = 2*H() + H(2)
sage: L.gram_matrix()

[0 1 0 0 0 0]
[1 0 0 0 0 0]
[0 0 0 1 0 0]
[0 0 1 0 0 0]
[0 0 0 0 0 2]
[0 0 0 0 2 0]

## Recovering the classical Eisenstein series:

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

## Computing isometry orbits for the discriminant group of L:

sage: L = Lattice(ZZ,2,[1,1,1])
sage: L.gram_matrix()
[2 1]
[1 2]
sage: L.isometry_orbits()
[[(0, 0)], [(1/3, 1/3), (2/3, 2/3)]]

## Computing the coefficients just once for each orbit above:

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

## Testing via the Siegel-Weil formula:

sage: L2 = (L + E(8))
sage: L2.theta_series_symmetrized(prec = 3)
{(0, 0, 0, 0, 0, 0, 0, 0, 0, 0): {0: 1, 1: 246, 2: 3600},
 (1/3, 1/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206},
 (2/3, 2/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206}}
sage: L2.eisenstein_series(5,prec = 3)
{(0, 0, 0, 0, 0, 0, 0, 0, 0, 0): {0: 1, 1: 246, 2: 3600},
 (1/3, 1/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206},
 (2/3, 2/3, 0, 0, 0, 0, 0, 0, 0, 0): {1/3: 3, 4/3: 723, 7/3: 7206}} 
