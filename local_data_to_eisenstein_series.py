"""
Classes and functions for finite quadratic modules such that their vector valued
Eisenstein series (w.r.t the Weil representation) can be computed.

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

from sage.all import Zmod, CC, RR, QQ, ZZ, is_odd, is_even, prod, infinity, Zp, valuation, \
    hilbert_symbol, floor, sqrt, Integer, identity_matrix, diagonal_matrix, block_diagonal_matrix, \
    matrix, Matrix, sign, I, pi
from sage.arith.misc import GCD, valuation, is_prime, is_squarefree, kronecker_symbol, moebius, sigma, CRT
from sage.functions.log                   import log, exp
from sage.quadratic_forms.special_values import quadratic_L_function__exact, gamma__exact, zeta__exact
from sage.rings.infinity import Infinity
from sage.rings.complex_number import ComplexNumber
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.sage_object           import SageObject

import itertools

class LocalSpaceByJordanData(SageObject):
    r"""
    This class mimics a lattice, by providing local data.

    INPUT:

    The constructor may be called in the following ways:

    #. ``LocalSpaceByJordanData(F.jordan_decomposition()._jordan_decomposition_data())``, where

       - `F` -- a finite quadratic module

    #. ``LocalSpaceByJordanData(J._jordan_decomposition_data())``, where

       - `J` -- the Jordan decomposition of a finite quadratic module

    EXAMPLES::

        sage: from finite_quadratic_module import FiniteQuadraticModule
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
    """
    def __init__(self, jordan_decomposition_data):
        self.__jd_with_basis = jordan_decomposition_data
        self.__jd = {q: self.__jd_with_basis[q][1] for q in self.__jd_with_basis.keys()}

    def _oddity(self, component):
        r"""
        Returns the oddity of the given Jordan component

        INPUT:

            (2,n,r,eps) or (2,n,r,eps,t) -- the data of a 2-adic Jordan component of the form (2^n)^(eps*r)_t

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L._oddity((2,1,2,1))
            0        
            sage: L._oddity((2,2,1,-1,3))
            3
            sage: L.oddity()
            3
        """
        if len(component) > 4:
            p, n, r, eps, t = component
        else:
            p, n, r, eps = component
            t = 0
        if eps == 1 or n%2 == 0:
            k = 0
        else:
            k = 1
        return (t+k*4) % 8

    def oddity(self):
        r"""
        Returns the oddity of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L._oddity((2,1,2,1))
            0        
            sage: L._oddity((2,2,1,-1,3))
            3
            sage: L.oddity()
            3
        """
        return sum(self._oddity(self.__jd[q]) for q in self.__jd.keys() if q % 2 == 0) % 8

    def _p_excess(self, component):
        r"""
        Returns the p-excess of the given Jordan component

        INPUT:

            (p,n,r,eps) -- the data of a p-adic Jordan component of the form (p^n)^(eps*r) for an odd prime p

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L._p_excess((3,1,1,-1))
            6
            sage: L.p_excess(3)
            6
        """
        p, n, r, eps = component
        if eps == 1 or n%2 == 0:
            k = 0
        else:
            k = 1
        return ((r*(p**n - 1)) + 4*k) % 8
            
    def p_excess(self, p):
        r"""
        Returns the p-excess of the underlying finite quadratic module

        INPUT:

            an odd prime

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L._p_excess((3,1,1,-1))
            6
            sage: L.p_excess(3)
            6
        """
        return sum(self._p_excess(self.__jd[q]) for q in self.__jd.keys() if q % p == 0) % 8

    def weil_index(self, p):
        r"""
        Returns the local Weil index of the underlying finite quadratic module for the prime p

        INPUT:

            a prime
    
        OUTPUT:

            an 8-th roor of unity
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.weil_index(2)
            (1/2*I - 1/2)*sqrt(2)
            sage: L.weil_index(3)
            I
            sage: L.weil_index(5)
            1
        """
        zeta_8 = exp(pi * I / 4)
        if p==2:
            return zeta_8**self.oddity()
        else:
            return zeta_8**-self.p_excess(p)

    def primes(self):
        r"""
        Returns the primes dividing the order of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            a list of primes
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.primes()
            [2, 3]
        """
        return Integer(prod(self.__jd.keys())).prime_divisors()
        
    def signature(self):
        r"""
        Returns the signature of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.signature()
            5
        """
        return (self.oddity() - sum(self.p_excess(p) for p in self.primes() if p != 2)) % 8

    def det(self):
        r"""
        Returns the order of the underlying finite quadratic module

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.det()
            48
        """
        return Integer(prod([q**self.__jd[q][2] for q in self.__jd.keys()]))
        
    def det_squarefree_part(self):
        r"""
        Returns the squarefree part of the order of the underlying finite quadratic module

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.det_squarefree_part()
            3
        """
        return self.det().squarefree_part()
        
    def kappa_sign(self):
        r"""
        Returns the sign of the discriminant of the underlying finite quadratic module

        INPUT:

            NONE

        OUTPUT:

            -1 or +1
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.kappa_sign()
            1
        """
        s = self.signature()
        if s % 2 == 0:
            return (-1)**(s / 2)
        else:
            return ((8-s)%4) - 2

    def kappa(self):
        r"""
        Returns an invariant usef for the computation of Eisenstein series.
        Modulo a factor of 2, this is the squarefree part of the discriminant of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            -1 or +1
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.kappa()
            6
        """
        case = self.signature() % 2
        return Integer(self.kappa_sign() * abs(self.det_squarefree_part()) * 2**(case *(1 - 2*self.det_squarefree_part().valuation(2))))
        
    def _local_gram_matrix(self, component):
        r"""
        Returns a choice of a local Gram matrix for the given component

        INPUT:

            (p,n,r,eps) or (p,n,r,eps,t) -- the data of a p-adic Jordan component of the form (p^n)^(eps*r)_t

        OUTPUT:

            a matrix
    
        """
        if len(component) > 4:
            p, n, r, eps, t = component
            if eps == +1:
                if t == 0:
                    tvalues = (1,7)
                elif t == 1:
                    tvalues = (1,)
                elif t == 2:
                    tvalues = (1,1)
                elif t == 3:
                    tvalues = (1,1,1)
                elif t == 4:
                    tvalues = (1,1,1,1)
                elif t == 5:
                    tvalues = (7,7,7)
                elif t == 6:
                    tvalues = (7,7)
                elif t == 7:
                    tvalues = (7,)
                else:
                    raise TypeError
            elif eps == -1:
                if t == 0:
                    tvalues = (5,1,1,1)
                elif t == 1:
                    tvalues = (3,7,7)
                elif t == 2:
                    tvalues = (3,7)
                elif t == 3:
                    tvalues = (3,)
                elif t == 4:
                    tvalues = (3,1)
                elif t == 5:
                    tvalues = (5,)
                elif t == 6:
                    tvalues = (5,1)
                elif t == 7:
                    tvalues = (5,1,1)
            return (p**n * diagonal_matrix(tvalues)).block_sum(self._local_gram_matrix([p,n,r-len(tvalues),1]))
        else:
            p, n, r, eps = component
            if p == 2:
                if eps == 1:
                    return p**n * block_diagonal_matrix([matrix(2,2,[0,1,1,0]) for j in range(0, r, 2)])
                else:
                    return (p**n * matrix(2,2,[2,1,1,2])).block_sum(self._local_gram_matrix([p,n,r-2,1]))
            else:
                if eps == -1:
                    a = (Zmod(p).quadratic_nonresidue() * 2).lift()
                    return 2 * p**n * diagonal_matrix([2 for j in range(r-1)] + [a])
                else:
                    return 4 * p**n * identity_matrix(r)
        
    def local_normal_form(self, p):
        r"""
        Returns a choice of a local Gram matrix with respect to the prime p

        INPUT:

            p -- a prime

        OUTPUT:

            a matrix
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.local_normal_form(3)
            [6]
        """
        return block_diagonal_matrix([self._local_gram_matrix(self.__jd[q]) for q in sorted([q for q in self.__jd.keys() if q % p == 0])])

    def valuation(self,i,p):
        """
        Gets the p-order of the (i,i)-entry in the diagonalized local normal form if p is odd.
        If p=2, get the 2-order of the of the upper right entry of the block containing the (i,i)-entry.

        INPUT:
            `i` -- an integer in range(self.dim())
        
            `p` -- a positive prime number

        OUTPUT:
            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.valuation(0,2)
            1
            sage: L.valuation(1,2)
            1
            sage: L.valuation(2,2)
            2
            sage: L.local_normal_form(3)
            [6]
            sage: L.valuation(0,3)
            1
        """
        S=self.local_normal_form(p)
        if p==2:
            if i < S.ncols()-1 and  S[i,i+1]!=0:
                return valuation(S[i,i+1], p)
            if i > 0 and S[i, i-1]!=0:
                return valuation(S[i,i-1], p)
        return valuation(S[i,i],p)
        
    def unit(self,i,p):
        """
        Gets the p-adic unit (=u) in the factorization of the (i,i)-entry (=2*u*p**e) in the diagonalized local normal form if p is odd.
        If p=2 and the (i,i)-entry is contained in a 2x2-block, return 1. If If the (i,i)-entry (=u*p**e) forms a 1x1 block, return
        the 2-adic unit (=u) in this factorization.

        INPUT:
            `i` -- an integer in range(self.dim())
        
            `p` -- a positive prime number

        OUTPUT:
            an integer
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.unit(0,2)
            1
            sage: L.unit(1,2)
            1
            sage: L.unit(2,2)
            3
            sage: L.local_normal_form(3)
            [6]
            sage: L.unit(0,3)
            1
        """
        S = self.local_normal_form(p)
        if p==2:
            if i < S.ncols()-1 and  S[i,i+1]!=0:
                return 1
            if i > 0 and S[i, i-1]!=0:
                return 1
            return p**(- self.valuation(i, p))*S[i,i]
        else:
            return p**(- self.valuation(i, p))*S[i,i] / 2
        
    def local_Q_p(self, element_tuple_p, p):
        """
        Evaluates the local quadratic form of the p-part of the underlying Jordan decomposition.

        INPUT:
            `element_tuple_p` -- a tuple
        
            `p` -- a positive prime number

        OUTPUT:
            a rational number
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.local_Q_p((0,0,0),2)
            0
            sage: L.local_Q_p((0,0,1/2),2)
            1/2
            sage: L.local_Q_p((0,0,1/4),2)
            3/8
        """
        v = matrix([element_tuple_p])
        q_value = (v * self.local_normal_form(p) * v.transpose())[0,0] / Integer(2)
        #print v
        #print self.local_normal_form(p)
        #print v * self.local_normal_form(p) * v.transpose()
        #print q_value
        return q_value - floor(q_value)
            
    def Q(self, element_dict_by_p):
        """
        Evaluates the local quadratic (defined mod 1) form of an element of the underlying Jordan decomposition.
        The element is expected to be a dictionary with prime keys.

        INPUT:
            `element_dict_by_p` -- a dictionary with prime keys and tuple values {p : tuple}

        OUTPUT:
            a rational number in [0,1)
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.local_normal_form(3)
            [6]
            sage: L.Q({2 : (0,0,0), 3: (0)})
            0
            sage: L.Q({2 : (0,0,0), 3: (1/3)})
            1/3
            sage: L.Q({2 : (0,0,0), 3: (2/3)})
            1/3
            sage: L.Q({2 : (1/2,0,0), 3: (0)})
            0
            sage: L.Q({2 : (1/2,1/2,0), 3: (0)})
            1/2
            sage: L.Q({2 : (1/2,1/2,0), 3: (1/3)})
            5/6
            sage: L.Q({2 : (1/2,1/2,1/2), 3: (1/3)})
            1/3
        """
        q_value = sum(self.local_Q_p(element_dict_by_p[p], p) for p in element_dict_by_p.keys())
        return q_value - floor(q_value)

    def group_structure(self, p):
        """
        Returns the group sturcture of the p-part of the underlying Jordan decomposition
        
        INPUT:
            `p` -- a prime
        
        OUTPUT:
            a list
    
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  2| 0]
            [ 2  0| 0]
            [-----+--]
            [ 0  0|12]
            sage: L.local_normal_form(3)
            [6]
            sage: L.group_structure(2)
            [2, 2, 4]
            sage: L.group_structure(3)
            [3]
        """
        result = []
        for q in sorted([q for q in self.__jd.keys() if q % p == 0]):
            result += self.__jd[q][2] * [q]
        return result

    def sort_2_adic(self):
        Q_loc = self.local_normal_form(2)
        n = Q_loc.ncols()
        even_I = [j for j in range(n) if Q_loc[j,j] == 0]
        even_II = sorted([j for j in range(n-1) if Q_loc[j,j+1] != 0 and not j in even_I] + [j for j in range(1, n) if Q_loc[j,j-1] != 0 and not j in even_I])
        odds = [j for j in range(n) if not j in (even_I + even_II)]
        return [odds, even_I, even_II]

    def discriminant_form_iterator(self):
        S = self.primes()
        d_p = [self.group_structure(p) for p in S]
        it1 = itertools.product(*[itertools.product(*[range(d_p[k][j]) for j in range(len(d_p[k]))]) for k in range(len(S))])
        it2 = itertools.imap(lambda x: {S[k] : tuple([x[k][j]/d_p[k][j] for j in range(len(d_p[k]))]) for k in range(len(S))}, it1)
        it3 = itertools.imap(lambda x: LocalSpaceByJordanDataElement(self, x), it2)
        return it3

    def discriminant_form_iterator_p(self, p):
        S = self.primes()
        d_p = [self.group_structure(pp) for pp in S]
        for j in range(len(S)):
            if S[j] != p:
                d_p[j] = [1 for k in range(len(d_p[j]))]
        it1 = itertools.product(*[itertools.product(*[range(d_p[k][j]) for j in range(len(d_p[k]))]) for k in range(len(S))])
        it2 = itertools.imap(lambda x: {S[k] : tuple([x[k][j]/d_p[k][j] for j in range(len(d_p[k]))]) for k in range(len(S))}, it1)
        it3 = itertools.imap(lambda x: LocalSpaceByJordanDataElement(self, x), it2)
        return it3

    def orbit_representatives_and_lengths(self, p):
        assert p > 2
        result = {}
        for el in self.discriminant_form_iterator_p(p):
            o = el.orbit_p(p)
            if o in result.keys():
                result[o][1] += 1
            else:
                result[o] = [el, 1]
        return result

    def whittaker_representatives_and_lengths(self, p):
        #assert p > 2
        result = {}
        for el in self.discriminant_form_iterator_p(p):
            o = tuple(el.Wpoly_invariants(p))
            #print el
            #print o
            if o in result.keys():
                result[o][1] += 1
            else:
                result[o] = [el, 1]
        return result

    def whittaker_orbit_lengths(self):
        S = self.primes()
        p_orbs = {p : self.whittaker_representatives_and_lengths(p) for p in S}
        result = []
        for orbs in itertools.product(*[p_orbs[p].keys() for p in S]):
            #print orbs
            #for j in range(len(S)):
            #    print S[j]
            #    print p_orbs[S[j]]
            #    print p_orbs[S[j]][orbs[j]]
            #    print p_orbs[S[j]][orbs[j]][1]
            result += [prod([p_orbs[S[j]][orbs[j]][1] for j in range(len(S))])]
        return result
                
class LocalSpaceByJordanDataElement(SageObject):

    def __init__(self, parent, entries_as_dict_by_p):
        self._entries = entries_as_dict_by_p
        self._parent = parent
        assert self._entries.keys() == self._parent.primes()

    def _repr_(self):
        return repr(self._entries)
        
    def __eq__(self, other):
        if other == 0:
            return all(all(j == 0 for j in self._entries[q]) for q in self._entries.keys())
        if not isinstance(other,type(self)):
            return False
        return self._parent == other._parent and self._entries == other._entries        

    def scale(self, p, fac):
        entries = {p : tuple(self._entries[p]) for p in self._entries.keys()}
        entries[p] = tuple([fac * j for j in self._entries[p]])
        return LocalSpaceByJordanDataElement(self._parent, entries)
        
    def integral_parent(self):
        return self._parent

    def Q(self):
        return self.integral_parent().Q(self._entries)

    def local_Q_p(self, p):
        return self.integral_parent().local_Q_p(self._entries[p], p)

    def norm(self):
        return self.Q()

    def order_p(self, p):
        return max(j.denominator() for j in self._mu_p(p))

    def multiplicity_reduced_norm_p(self, p, k, allow_2 = False):
        if p == 2 and not(allow_2):
            raise ValueError, "p should not be 2, given {0}.".format(p)
        gs = self._parent.group_structure(p)
        n = len(gs)
        ab_gp_pres = [Integer(self._mu_p_i(p, i) * gs[i]) for i in range(n)]
        image_pk = [((ab_gp_pres[i] * p**k) % gs[i]) for i in range(n)]
        m = p**(GCD(image_pk).valuation(p) - k)
        preimage = [image_pk[i] / m / p**k / gs[i] for i in range(n)]
        q_red = m * p**k * self._parent.local_Q_p(preimage, p)
        q_red -= floor(q_red)
        #print self, p, k, p**k, image_pk, m, preimage, q_red
        return m, q_red
        
    def multiplicity_p(self, p, k = 0):
        return self.multiplicity_reduced_norm_p(p, k, allow_2 = True)[0]
        
    def reduced_norm_p(self, p, k = 0):
        return self.multiplicity_reduced_norm_p(p, k, allow_2 = False)[1]        

    def orbit_p(self, p):
        assert p > 2
        maxk = self.order_p(p).valuation(p)
        orb = [p**maxk]
        orb += [self.multiplicity_p(p, k) for k in range(maxk)]
        orb += [self.reduced_norm_p(p, k) for k in range(maxk)]
        orb = tuple(orb)
        return orb
        
    def order(self):
        return prod(self.p_order(p) for p in self.integral_parent().primes())
        
    def _mu_p(self, p):
        return self._entries[p]

    def _mu_p_i(self, p, i):
        return self._entries[p][i]

    def H(self, p):
        if p==2:
            [odds, even_I, even_II] = self.integral_parent().sort_2_adic()
            Hs = [j for j in odds if self._mu_p_i(p, j).valuation(p) >= 0]
            Ms = [j for j in even_I[0::2] if self._mu_p_i(p, j).valuation(p) >= 0 and self._mu_p_i(p, j+1).valuation(p) >= 0]
            Ns = [j for j in even_II[0::2] if self._mu_p_i(p, j).valuation(p) >= 0 and self._mu_p_i(p, j+1).valuation(p) >= 0]
            return {'H':Hs, 'M':Ms, 'N':Ns}
        else:
            return [i for i in range(len(self._mu_p(p))) if self._mu_p_i(p, i).valuation(p) >= 0]
        
    def L(self, k, p):
        if p==2:
            return [i for i in self.H(p)['H']
                    if (self.integral_parent().valuation(i,p)-k) < 0 and is_odd(self.integral_parent().valuation(i,p)-k)]
        else:
            return [i for i in self.H(p)
                    if (self.integral_parent().valuation(i,p)-k) < 0 and is_odd(self.integral_parent().valuation(i,p)-k)]
        
    def l(self, k, p):
        return len(self.L(k,p))

    def d(self, k, p):
        if p==2:
            return (k
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['H']])/Integer(2)
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['M']])
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['N']]))
        else:
            return k + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)])/Integer(2)

    def eps(self, k, p):
        if p==2:
            return prod([self.integral_parent().unit(j, p) for j in self.L(k, p)])
        else:
            return ((self.modified_hilbert_symbol(-1,p)**floor((self.l(k,p)/2)))
                    * prod([self.modified_hilbert_symbol(self.integral_parent().unit(i,p),p) for i in self.L(k,p)]))

    def K0(self, p):
        #n = self.integral_parent().dimension()
        n = len(self._mu_p(p))
        if p==2:
            if n == len(self.H(p)['H'])+2*len(self.H(p)['M'])+2*len(self.H(p)['N']):
                return Infinity
            else:
                [odds, even_I, even_II] = self.integral_parent().sort_2_adic()
                return (min([self.integral_parent().valuation(i,p) + self._mu_p_i(p,i).valuation(p)
                             for i in odds if self._mu_p_i(p,i).valuation(p) < -1]
                            + [self.integral_parent().valuation(i,p) for i in odds if self._mu_p_i(p,i).valuation(p) == -1]
                            + [self.integral_parent().valuation(i,p)
                               + min([self._mu_p_i(p,i).valuation(p), self._mu_p_i(p,i+1).valuation(p)])
                               for i in even_I[0::2] if i not in self.H(p)['M']]
                            + [self.integral_parent().valuation(i,p)
                               + min([self._mu_p_i(p,i).valuation(p), self._mu_p_i(p,i+1).valuation(p)])
                               for i in even_II[0::2] if i not in self.H(p)['N']]))
        else:
            if n == len(self.H(p)):
                return Infinity
            else:
                return min([self.integral_parent().valuation(i,p) + self._mu_p_i(p,i).valuation(p)
                            for i in range(n) if i not in self.H(p)])

    def p(self, k):
        return (-1)**sum([min([self.integral_parent().valuation(i,2)-k,0]) for i in self.H(2)['N']])

    def delta(self, k):
        for j in self.H(2)['H']:
            if k == self.integral_parent().valuation(j,2):
                return 0
        return 1

    def modified_hilbert_symbol(self, a, p):
        if Zp(p)(a).is_unit():
            return hilbert_symbol(a,p,p)
        else:
            return 0

    def f1(self, x, p):
        a=valuation(x,p)
        if is_even(self.l(a+1,p)):
            return -1/p
        else:
            return self.modified_hilbert_symbol(x * p**-a,p)/sqrt(p)

    def t(self, m, p):
        n = len(self._mu_p(p))
        #n = self.integral_parent().dimension()
        if p==2:
            [odds, even_I, even_II] = self.integral_parent().sort_2_adic()
            return (m
                    - sum([self.integral_parent().unit(i,p)*p**(self.integral_parent().valuation(i,p)-1)
                           *(self._mu_p_i(p,i))**2
                           for i in odds if i not in self.H(p)['H']])
                    - sum([p**(self.integral_parent().valuation(i,p))
                           *(self._mu_p_i(p,i) * self._mu_p_i(p,i+1))
                           for i in even_I[0::2] if i not in self.H(p)['M']])
                    - sum([p**(self.integral_parent().valuation(i,p))
                           *(self._mu_p_i(p,i)**2 + self._mu_p_i(p,i) * self._mu_p_i(p,i+1) + self._mu_p_i(p,i+1)**2)
                           for i in even_II[0::2] if i not in self.H(p)['N']])
                    )
        else:
            return (m
                    - sum([self.integral_parent().unit(i,p)*p**(self.integral_parent().valuation(i,p))
                           *(self._mu_p_i(p,i))**2
                           for i in range(n) if i not in self.H(p)])
                    )

    def nu(self, m, k):
        return (self.t(m, 2) * 2**(Integer(3)-k)
                - sum([self.integral_parent().unit(j,2)
                       for j in self.H(2)['H']
                       if self.integral_parent().valuation(j,2) < k])
                )

    def Wpoly(self, p, m, verbose=False):
        R = PolynomialRing(QQ, 'X')
        if (m-self.Q()).valuation(p) < 0:
            return R(0)
            
        t=self.t(m,p)
        a = valuation(t,p)
        n = len(self._mu_p(p))
        #print "n:", n, type(n)
        if verbose:
            print "t=",t
            print "a=",a
        XX = R.gen()

        if p==2:
            
            k0 = min(self.K0(p), a+3)
            if verbose:
                print "k0=", k0
            if k0 < Infinity:
                result = R(1)
                for k in range(1, k0+1):
                    if is_even(self.l(k,p)):
                        if verbose:
                            print "k=", k
                            print "delta=", self.delta(k)
                            print "L=", self.L(k,p)
                            print "l=", self.l(k,p)
                            print "d=", self.d(k,p)
                            print "d-1=", self.d(k,p) - 1
                            print "eps=", self.eps(k,p)
                            print "nu",type(self.nu(m,k)), self.nu(m,k), Integer(Zp(2)(self.nu(m,k)))
                        if self.nu(m,k).valuation(2) >= 3:  #This does not work porperly: self.nu(m, k) % 8 == 0:
                            result += (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-1)
                                       * kronecker_symbol(2, self.eps(k,p)) * XX**k
                                       )
                        elif (self.nu(m,k)-4).valuation(2) >= 3:  #This does not work porperly: self.nu(m, k) % 8 == 4:
                            result -= (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-1)
                                       * kronecker_symbol(2, self.eps(k,p)) * XX**k
                                       )
                    else:
                        if verbose:
                            print "k=", k
                            print "delta=", self.delta(k)
                            print "L=", self.L(k,p)
                            print "l=", self.l(k,p)
                            print "d=", self.d(k,p)
                            print "d-3/2=", self.d(k,p) - 3/Integer(2)
                            print "eps=", self.eps(k,p)
                            print "nu",type(self.nu(m,k)), self.nu(m,k), Integer(Zp(2)(self.nu(m,k)))
                        result += (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-3/Integer(2))
                                   * kronecker_symbol(2, self.eps(k,p)*Integer(Zp(2)(self.nu(m,k)))) * XX**k
                                   )
                return result
            else:
                l = max(self.integral_parent().valuation(i,p) for i in range(n))
                #From k0 to K0=Infinity, the above "sum" is a geometric series.
                #For simplicity in the following code, k0 is even: 
                k0 = l+1+(l+1)%2

                result = R(1)
                for k in range(1, k0):
                    if is_even(self.l(k,p)):
                        if self.nu(m, k) % 8 == 0:
                            result += (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-1)
                                       * kronecker_symbol(2, self.eps(k,p)) * XX**k
                                       )
                        elif self.nu(m, k) % 8 == 4:
                            result -= (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-1)
                                       * kronecker_symbol(2, self.eps(k,p)) * XX**k
                                       )
                    else:
                        result += (self.delta(k) * self.p(k) * 2**Integer(self.d(k,p)-3/Integer(2))
                                   * kronecker_symbol(2, self.eps(k,p)*Integer(Zp(2)(self.nu(m,k)))) * XX**k
                                   )
                        
                l_even = self.l(k0,p)
                l_odd = self.l(k0+1,p)
                d = sum(self.integral_parent().valuation(i,p) for i in self.H(p)['H'])/Integer(2)
                d += sum(self.integral_parent().valuation(i,p) for i in self.H(p)['M'])
                d += sum(self.integral_parent().valuation(i,p) for i in self.H(p)['N'])
                eps_even = self.eps(k0,p)
                eps_odd = self.eps(k0+1,p)
                p_even = self.p(k0)
                p_odd = self.p(k0+1)
                nu_even_odd = Integer(self.nu(m, k0)) % 8
                if nu_even_odd == 0:
                    psi_times_char_nu = +1
                elif nu_even_odd == 4:
                    psi_times_char_nu = -1
                else:
                    psi_times_char_nu = 0
                    
                # In the following cases we evaluate (the meromorphic extension of) the geometric series for even resp. odd k
                if l_even % 2 == 0:
                    result += (p_even * p**Integer(d-1 + (1-n/2)*k0)
                               * kronecker_symbol(2, eps_even)
                               * psi_times_char_nu * XX**k0
                               / (1 - p**(2-n) * XX**2)
                               )
                else:
                    result += (p_even * p**Integer(d-3/Integer(2) + (1-n/2)*k0)
                               * kronecker_symbol(2, eps_even * nu_even_odd) * XX**k0
                               / (1 - p**(2-n) * XX**2)
                               )
                if l_odd % 2 == 0:
                    result += (p_odd * p**Integer(d-1 + (1-n/2)*(k0+1))
                               * kronecker_symbol(2, eps_odd)
                               * psi_times_char_nu * XX**(k0+1)
                               / (1 - p**(2-n) *XX**2)
                               )
                else:
                    result += (p_odd * p**Integer(d-3/Integer(2) + (1-n/2)*(k0+1))
                               * kronecker_symbol(2, eps_odd * nu_even_odd) * XX**(k0+1)
                               / (1 - p**(2-n) * XX**2)
                               )
                return result
                        
        else:
            
            if a >= 0  and a < self.K0(p):
                result = (R(1)
                          + R(1-1/Integer(p)) * sum([self.eps(k,p)*(p**self.d(k,p))*XX**k
                                                     for k in range(1,a+1) if is_even(self.l(k,p))])
                          )
                result += self.eps(a+1,p)*R(self.f1(t,p)*p**self.d(a+1,p))*XX**(a+1)

                return result
            elif self.K0(p) < Infinity:
                return (R(1)
                        + R(1-1/Integer(p)) * sum([self.eps(k,p)*(p**self.d(k,p))*XX**k
                                                   for k in range(1,self.K0(p)+1) if is_even(self.l(k,p))])
                        )
            else:
                l = max(self.integral_parent().valuation(i,p) for i in range(n))
                #From k0 to K0=Infinity, the above "sum" is a geometric series.
                #For simplicity in the following code, k0 is even:
                k0 = l+1+(l+1)%2
                l_even = self.l(k0,p)
                l_odd = self.l(k0+1,p)
                d = sum(self.integral_parent().valuation(i,p) for i in self.H(p))/Integer(2)
                result = (R(1)
                          + QQ(1-1/Integer(p)) * sum([self.eps(k,p)*(p**self.d(k,p))*XX**k
                                                      for k in range(1,k0) if is_even(self.l(k,p))])
                          )
                eps_even = self.eps(k0,p)
                eps_odd = self.eps(k0+1,p)
                    
                # In the following cases we evaluate (the meromorphic extension of) the geometric series for even resp. odd k
                if l_even % 2 == 0:
                    #print "Place" + 20*"4"
                    result += (R(1-1/Integer(p)) * eps_even
                               * p**Integer(d+(1-n/2)*k0) * XX**k0
                               / (1 - p**(2-n) * XX**2)
                               )
                if l_odd % 2 == 0:
                    #print "Place" + 20*"5"
                    result += (R(1-1/Integer(p)) * eps_odd
                               * p**Integer(d+(1-n/2)*(k0+1)) * XX**(k0+1)
                               / (1 - p**(2-n) *XX**2)
                               )
                return result
            
        raise RuntimeError, "A result should already have been returend."

    def W(self, p, m, s, min_precision=53):
        wpoly = self.Wpoly(p, m)
        
        if type(s) == ComplexNumber:
            return wpoly(p**(-s))
            
        if s in QQ:
            
            sden = (-s).denominator()
            snum = (-s).numerator()
            X = wpoly.parent().gen()

            # The polynomial X**sden - p**snum is irreducible, thus we reduce wpoly by it to take a closer look at wpoly(p**(snum/sden))
            resultpoly = wpoly % (X**sden - p**snum)

            assert wpoly(p**-s)==resultpoly(p**-s)

            wpoly = resultpoly
            
            if wpoly.is_constant():
                return wpoly.constant_coefficient()
                
        if min_precision < 0:
            raise ValueError, "precision is less than 0. Given: {0}".format(min_precision)
                
        prec = max(0,log(abs(wpoly(p**-s)), 2)) + min_precision
        resultcomplex = ComplexField(prec)(wpoly(p**-s))

        return resultcomplex

    def _Wpoly_invariants(self, p):
        order = self.order_p(p)
        Qfloor = self.Q()
        #localQfloor = self.local_Q_p(p)
        #print "Qfloor:", Qfloor, "localQfloor:", localQfloor, Qfloor == localQfloor
        invariants = [order]
        k0 = self.K0(p)
        if p == 2 and k0 != Infinity:
            k0 = self.multiplicity_p(2).valuation(2) + 1
        if k0 == Infinity:
            k0 = 1
            offset = 1
        else:
            offset = 0
        for m in range(offset, offset + p**k0):
            invariants += [(m + Qfloor, self.Wpoly(p, m + Qfloor))]
        return tuple(invariants)

    def Wpoly_invariants(self, p):
        return [(p**k, self.scale(p, p**k)._Wpoly_invariants(p)) for k in range(self.order_p(p).valuation(p))]

    def eisenstein_series(self, weight, allow_weight_2 = True, prec=10, verbose=False):
        if verbose:
            print "weight:", weight, type(weight)
        parent = self.integral_parent()
        coefficients = [Integer(m) for m in range(prec)]

        l = QQ(weight)
        if l.is_integer():
            l = ZZ(l)
        if verbose:
            print "l:", l, type(l)
        if l < 2 or (l == 2 and not allow_weight_2) :
            raise NotImplementedError, "l should be > 2. l=" + l.str()

        s = Integer(parent.signature())
        case = s % 2 # If case == 1, we are dealing with the odd case. If case == 0, we are dealing with the odd case.
        kappa = parent.kappa()
        if verbose:
            print "kappa:", kappa

        if case:
            #Checking conditon (2.10) in [KY]
            if l.denominator() != 2 or (((Integer(2 * l) - kappa.sign()) % 4) != 0):
                raise NotImplementedError, "l=" + l.str() + ", kappa=" + kappa.str()
        else:
            #Checking conditon (2.10) in [KY]
            if not l.is_integer() or ((-1)**l != kappa.sign()):
                raise NotImplementedError, "l=" + l.str() + ", kappa=" + kappa.str()

        S = parent.primes()

        if verbose:
            print "S:", S

        def b(p, m, s, D, kappa = kappa):
            d = (kappa * m).squarefree_part()
            #d = Integer(d.numerator()*d.denominator()) # This should not be necessary
            if (d-1) % 4 != 0:
                d *= 4
            c = (4 * kappa * m / d).sqrt()
            vp = kronecker_symbol(d,p)
            X = p**(-s)
            k = c.valuation(p) 
            if k < 0:
                return 1
            elif D % p != 0:
                return (1 - vp*X + p**k*vp*X**(1+2*k) - p**(k+1)*X**(2*k+2)) / (1 - p*X**2)
            else:
                return ((1 - vp*X)*(1 - p**2*X**2) - p**(k+1)*vp*X**(1+2*k) + p**(k+2)*X**(2*k+2) + vp*p**(k+1)*X**(2*k+3) - p**(2*k+2)*X**(2*k+4)) / (1 - p*X**2)
                
        if verbose:
            print "(-2 * pi * I)**l:"
            print (-2 * pi * I)**l
            print "gamma__exact(l):"
            print gamma__exact(l),
        fac = 2**l * pi**l * exp(-l / 2 * pi * I) / gamma__exact(l)
        if verbose:
            print "fac:", fac

        result = {}
        
        #The odd case:
        if case:
            fac /= zeta__exact(Integer(2*l - 1))
            for p in S:
                if verbose:
                    print "p:", p
                fac *= parent.weil_index(p) * p**(-parent.det().valuation(p)/Integer(2)) / (1 - p**Integer(1 - 2*l))
            fac = {0 : fac}
            #L_values = dict()
            if verbose:
                print "odd case"
                print fac
                print "lattice_element:", self
            offset = self.Q() - floor(self.Q())
            result = {}
            for m in [offset + j for j in coefficients]:
                if verbose:
                    print "m:", m
                if m == 0:
                    if self == 0:
                        result[m] = 1
                    #else:
                    #    result[tuple(lattice_element)][m] = 0
                else:
                    if not m in fac.keys():
                        d = (kappa * m).squarefree_part()                            
                        #d = Integer(d.numerator()*d.denominator()) # This should not be necessary
                        if (d-1) % 4 != 0:
                            d *= 4
                        #if not d in L_values.keys():
                        #    L_values[d] = quadratic_L_function__exact(floor(l), d)
                        #    for p in S:
                        #        L_values[d] *= (1 - kronecker_symbol(d,p) * p**(- floor(l)))
                        if verbose:
                            print "Dirichlet Character: d=", d
                        L_value = quadratic_L_function__exact(floor(l), d)
                        for p in S:
                            L_value *= (1 - kronecker_symbol(d,p) * p**(- floor(l)))
                        if verbose:
                            print "m**(l-1):", m**(l-1)
                        #fac[m] = m**(l-1) * L_values[d]
                        fac[m] = m**(l-1) * L_value
                        #res = fac * m**(l-1) * L_values[d]
                        if verbose:
                            print "m**(l-1) * L_value:", fac[m]
                            factors = dict()
                            factors[0] = [fac, m**(l-1), quadratic_L_function__exact(floor(l), d), 1 / zeta__exact(Integer(2*l - 1))]
                            #print "1:", res
                            #res /= (1 - p**Integer(1 - 2*l)) / (1 - kronecker_symbol(d,p) * p**(- floor(l)))
                        #    if verbose:
                        #        factors[p]=[1 / (1 - p**Integer(1 - 2*l))]
                        #        factors[p].append((1 - kronecker_symbol(d,p) * p**(- floor(l))))
                        #        print "2:", p, res
                        #    res *= lattice_element.W(p, m, Integer(l - n/Integer(2))) * self.weil_index(p) * p**(-self.det().valuation(p)/2)
                        #    if verbose:
                        #        factors[p].append(lattice_element.W(p, m, Integer(l - n/Integer(2))))
                        #        factors[p].append(self.weil_index(p))
                        #        factors[p].append(p**(-self.det().valuation(p)/2))
                        #        print "3:", p, res
                        for p in (2*m.numerator()).prime_divisors():
                            if not p in S:
                                fac[m] *= b(p, m, floor(l) , 1)
                                #res *= b(p, m, floor(l) , 1)
                                if verbose:
                                    factors[p]=(b(p, m, floor(l), 1))
                                    print "p, b(p,m,...)", p, factors[p]
                                #    print "4:", p, res
                    res = fac[0]*fac[m]
                    if verbose:
                        print "Current result:", res
                    for p in S:
                        res *= self.W(p, m, Integer(l - len(self._mu_p(p))/Integer(2)))
                        if verbose:
                            print "res*W_" + str(p) + ":", res
                    res = res.simplify()
                    res = sign(RR(res)) * sqrt(QQ(res**2))
                    res = QQ(res)
                    if res != 0:
                        result[m] = res #(res, factors) #QQ(res)
                    if verbose:
                        print "factors:", factors

        #The even case:
        else:
            if verbose:
                print "even case"
            d = kappa.squarefree_part()
            #d = Integer(d.numerator()*d.denominator()) # This should not be necessary
            if (d-1) % 4 != 0:
                d *= 4
            fac /= quadratic_L_function__exact(l,d)
            for p in S:
                fac /= (1 - kronecker_symbol(d,p) * p**(-l))
            if verbose:
                print "kappa:", kappa
                print "d:    ", d
                print "fac:  ", fac
            if verbose:
                print "lattice_element:", self
            offset = self.Q() - floor(self.Q())
            result = {} #{-1 : offset}
            for m in [offset + j for j in coefficients]:
                if m == 0:
                    if self == 0:
                        result[m] = 1
                    #else:
                    #    result[tuple(lattice_element)][m] = 0
                else:
                    res = fac * m**(l-1)
                    for p in S:
                        res *= self.W(p, m, Integer(l - len(self._mu_p(p))/2)) * parent.weil_index(p) * p**(-parent.det().valuation(p)/2)
                    for p in m.numerator().prime_divisors():
                        if not p in S:
                            res *= sum([(hilbert_symbol(p, kappa, p) * p**(1-l))**Integer(r) for r in range(m.valuation(p)+1)])
                    #for p in m.denominator().prime_divisors():
                    #    if not p in S:
                    #        res /= sum([(hilbert_symbol(p, kappa, p) * p**(1-l))**Integer(r) for r in range(m.valuation(p)+1)])
                    res = res.simplify()
                    res = sign(RR(res)) * sqrt(QQ(res**2))
                    res = QQ(res)
                    if res != 0:
                        result[m] = res #(res, RR(res))#QQ(res)
        #print ds
        #if elements == None and coefficient == None:
        #    self._lattice_data['eisenstein_prec'][l] = prec
        #    self._lattice_data['eisenstein_series'][l] = result                            
        return result
