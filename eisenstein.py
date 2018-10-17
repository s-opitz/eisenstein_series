"""
Classes and functions for (even) lattices such that their vector valued
Eisenstein series (w.r.t the Weil representation) can be computed.
Symmetrized vector valued theta series can also be computed, the Siegel Weil Formula
provides test cases.

AUTHORS:

- Sebastian Opitz
"""

#*****************************************************************************
#       Copyright (C) 2018 Sebastian Opitz
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.all import matrix, Integer
from sage.structure.sage_object           import SageObject
from finite_quadratic_module import FiniteQuadraticModule
from genus_symbol import GenusSymbol
from local_data_to_eisenstein_series import LocalSpaceByJordanData
from integer_lattice import Lattice

class EisensteinSeries(SageObject):
    """
    A simple container/constructor for the Fourier coefficients of vector valued Eisenstein series.

    INPUT:

    The constructor may be called in the following way:

    #. ``EisensteinSeries(data)``, where

        `data` - a dictionary of dictionary of the form {element : {q-power : corresponding coefficient}, ...}

    #. ``EisensteinSeries(data, weight, prec, dual)``, where

        `data` - a string representing a genus symbol or the Gram matrix of an even lattice

        `weight` - the weight for which to compute the Eisenstein series

        `prec` - the precision up to which to the Eisenstein series is computed

        `dual` - decides whether to use the Weil or the dual Weil representation (default: False)

    EXAMPLES::

        sage: EisensteinSeries('', 4)

        A vector valued q-series with coefficients
        (): 1 q^(0) + 240 q^(1) + 2160 q^(2) + O(q^(3))

        sage: EisensteinSeries(matrix(2,2,[2,1,1,2]), weight = 5)

        A vector valued q-series with coefficients
        (0, 0): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
        (1/3, 1/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
        (2/3, 2/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))

        sage: EisensteinSeries(- matrix(2,2,[2,1,1,2]), weight = 5, dual = True)

        A vector valued q-series with coefficients
        (0, 0): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
        (1/3, 1/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
        (2/3, 2/3): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))


        sage: EisensteinSeries('3^-1', 5)

        A vector valued q-series with coefficients
        ((3, (0, 0, 0, 0)),): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
        ((3, (0, 0, 0, 1/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
        ((3, (0, 0, 0, 2/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))

        sage: EisensteinSeries('3^1', 5, dual = True)

        A vector valued q-series with coefficients
        ((3, (0, 0, 0, 0)),): 1 q^(0) + 246 q^(1) + 3600 q^(2) + O(q^(3))
        ((3, (0, 0, 0, 1/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
        ((3, (0, 0, 0, 2/3)),): 3 q^(1/3) + 723 q^(4/3) + 7206 q^(7/3) + O(q^(10/3))
    
        sage: EisensteinSeries({'badabing' : {3 : 'badabum'}})

        A vector valued q-series with coefficients
        badabing: badabum q^(3) + O(q^(4))

    """
    def __init__(self, data, weight = None, prec = 3, dual = False):
        if isinstance(data, dict):
            #print "dict"
            self._coeff_dict = data
        elif isinstance(data, str):
            #print "str"
            try:
                if data == '':
                    F = FiniteQuadraticModule(matrix(2,2,[0,1,1,0]))
                else:
                    F = FiniteQuadraticModule(data)
                if dual:
                    F = F.twist(Integer(-1))
                J = F.jordan_decomposition()
                L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            except:
                jd = genus_symbol_dict_to_jd(GenusSymbol(data)._symbol_dict)
                L = LocalSpaceByJordanData(jd)
            self._coeff_dict = L.eisenstein_series(weight, prec = prec)
        else:
            #print "else"
            L = Lattice(data)
            if dual:
                L = L(-1)
            self._coeff_dict = L.eisenstein_series(weight, prec = prec)
        
    def _repr_(self):
        result = 'A vector valued q-series with coefficients\n'
        for el in sorted(self._coeff_dict.keys()):
            d = self._coeff_dict[el]
            result += str(el) + ": " + dict_to_q_series(d) + '\n'
        return result

def dict_to_q_series(d):
    s = ''
    for power in sorted(d.keys()):
        coeff = d[power]
        if coeff != 0:
            s += str(d[power]) + ' q^(' + str(power) + ') + '
    s += 'O(q^(' + str(power + 1) + '))'
    return s

def genus_symbol_dict_to_jd(d):
    result = {}
    for p in d.keys():
        for c in d[p]:
            if p == 2:
                n, r, eps, b, t = c
                if b:
                    result[p**n] = ((), (p, n, r, eps, t))
                else:
                    result[p**n] = ((), (p, n, r, eps))
            else:
                n, r, eps = c
                result[p**n] = ((), (p, n, r, eps))
    return result