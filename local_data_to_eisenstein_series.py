from sage.all import Zmod, CC, RR, QQ, ZZ, is_odd, is_even, prod, infinity, Zp, valuation, \
    hilbert_symbol, floor, sqrt, Integer, identity_matrix, diagonal_matrix, block_diagonal_matrix, \
    matrix, Matrix, sign, I, pi, squarefree_part, factor, QuadraticForm, DiagonalQuadraticForm, \
    vector, denominator, gcd, frac, zeta
from sage.arith.misc import GCD, LCM, valuation, is_prime, is_squarefree, kronecker_symbol, moebius, sigma, CRT
from sage.functions.log                   import log, exp
from sage.functions.transcendental import zeta
from sage.quadratic_forms.special_values import quadratic_L_function__exact, gamma__exact, zeta__exact
from sage.rings.infinity import Infinity
from sage.rings.complex_number import ComplexNumber
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.sage_object           import SageObject

from sage.misc.cachefunc import cached_function, cached_method

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

    @cached_method
    def _cache_key(self):
        return tuple([(q, self.__jd[q]) for q in sorted(self.__jd.keys())])

    @cached_method
    def _oddity(self, component):
        r"""
        Returns the oddity of the given Jordan component

        INPUT:

            (2,n,r,eps) or (2,n,r,eps,t) -- the data of a 2-adic Jordan component of the form (2^n)^(eps*r)_t

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

    @cached_method
    def oddity(self):
        r"""
        Returns the oddity of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

    @cached_method
    def p_excess(self, p):
        r"""
        Returns the p-excess of the underlying finite quadratic module

        INPUT:

            an odd prime

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
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
        #zeta_8 = CyclotomicField(8).gen()
        if p==2:
            return zeta_8**self.oddity()
        else:
            return zeta_8**-self.p_excess(p)

    @cached_method
    def primes(self):
        r"""
        Returns the primes dividing the order of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            a list of primes
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.primes()
            [2, 3]
        """
        return Integer(prod(self.__jd.keys())).prime_divisors()

    @cached_method
    def signature(self):
        r"""
        Returns the signature of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.signature()
            5
        """
        return (self.oddity() - sum(self.p_excess(p) for p in self.primes() if p != 2)) % 8

    @cached_method
    def det(self):
        r"""
        Returns the order of the underlying finite quadratic module

        INPUT:

            NONE

        OUTPUT:

            an integer
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.det_squarefree_part()
            3
        """
        return self.det().squarefree_part()

    @cached_method
    def kappa_sign(self):
        r"""
        Returns the sign of the discriminant of the underlying finite quadratic module

        INPUT:

            NONE

        OUTPUT:

            -1 or +1
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.kappa_sign()
            1
        """
        s = self.signature()
        if s % 2 == 0:
            return Integer(-1)**(s / 2)
        else:
            return ((8-s)%4) - 2

    @cached_method
    def kappa(self):
        r"""
        Returns an invariant usef for the computation of Eisenstein series.
        Modulo a factor of 2, this is the squarefree part of the discriminant of the underlying finite quadratic module.

        INPUT:

            NONE

        OUTPUT:

            -1 or +1
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
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

        EXAMPLES::

            sage: L._local_gram_matrix((2,1,2,1))

            [0 2]
            [2 0]
            sage: L._local_gram_matrix((2,1,2,-1))

            [4 2]
            [2 4]
            sage: L._local_gram_matrix((2,2,1,-1,3))
            [12]
            sage: L._local_gram_matrix((2,2,3,-1,3))
            
            [12  0  0]
            [ 0  0  4]
            [ 0  4  0]
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

    @cached_method
    def local_normal_form(self, p):
        r"""
        Returns a choice of a local Gram matrix with respect to the prime p

        INPUT:

            p -- a prime

        OUTPUT:

            a matrix
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]

        """
        result = block_diagonal_matrix([self._local_gram_matrix(self.__jd[q]) for q in sorted([q for q in self.__jd.keys() if q % p == 0])])
        n = result.ncols()
        if p == 2:
            if (self.signature() + n) % 2 != 0:
                raise RuntimeError, 'Unable to find a Gram Matrix of a dimension which has the same parity as the signature.'
            d = self.det().abs() / result.det() * self.kappa_sign() * Integer(-1)**((n+2)*(n+1)/2)
            d = d.squarefree_part()
            d = d % 8
            if d == 7:
                return matrix(2,2,[0, 1, 1, 0]).block_sum(result)
            elif d == 3:
                return matrix(2,2,[2, 1, 1, 2]).block_sum(result)
            else:
                raise RuntimeError, 'We do not know what to do in this case yet, maybe it should never occur!'
        else:
            if (self.signature() + n) % 2 != 0:
                result = matrix(1,1,[4]).block_sum(result)
            n = result.ncols()
            eps1 = 2 * self.det().abs() / result.det() * self.kappa_sign() * Integer(-1)**((n+2)*(n+1)/2)
            eps1 = eps1.squarefree_part()
            return matrix(2,2,[2*eps1, 0, 0, 4]).block_sum(result)

    @cached_method
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.valuation(0,2)
            0
            sage: L.valuation(1,2)
            0
            sage: L.valuation(2,2)
            1
            sage: L.valuation(3,2)
            1
            sage: L.valuation(4,2)
            2
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]
            sage: L.valuation(0,3)
            0
            sage: L.valuation(1,3)
            0
            sage: L.valuation(2,3)
            1

        """
        S=self.local_normal_form(p)
        if p==2:
            if i < S.ncols()-1 and  S[i,i+1]!=0:
                return valuation(S[i,i+1], p)
            if i > 0 and S[i, i-1]!=0:
                return valuation(S[i,i-1], p)
        return valuation(S[i,i],p)

    @cached_method
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.unit(0,2)
            1
            sage: L.unit(1,2)
            1
            sage: L.unit(2,2)
            1
            sage: L.unit(3,2)
            1
            sage: L.unit(4,2)
            3
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]
            sage: L.unit(0,3)
            -1
            sage: L.unit(1,3)
            2
            sage: L.unit(2,3)
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

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_Q_p((0,0,0,0,0),2)
            0
            sage: L.local_Q_p((0,0,0,0,1/2),2)
            1/2
            sage: L.local_Q_p((0,0,0,0,1/4),2)
            3/8
            sage: L.local_Q_p((0,0,1,1,0),2)
            0
            sage: L.local_Q_p((1,1,1,1,1),2)
            0

        """
        v = matrix([element_tuple_p])
        q_value = (v * self.local_normal_form(p) * v.transpose())[0,0] / Integer(2)
        #print v
        #print self.local_normal_form(p)
        #print v * self.local_normal_form(p) * v.transpose()
        #print q_value
        return q_value - floor(q_value)

    def local_B_p(self, element_tuple_p, other_element_tuple_p, p):
        """
        Evaluates the local bilinear form of the p-part of the underlying Jordan decomposition.

        INPUT:
            `element_tuple_p` -- a tuple

            `other_element_tuple_p` -- a tuple
        
            `p` -- a positive prime number

        OUTPUT:
            a rational number
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_B_p((0,0,1/2,0,0),(0,0,0,1/2,0),2)
            1/2

        """
        v = matrix([element_tuple_p])
        other_v = matrix([other_element_tuple_p])
        b_value = (v * self.local_normal_form(p) * other_v.transpose())[0,0]
        #print v
        #print self.local_normal_form(p)
        #print v * self.local_normal_form(p) * v.transpose()
        #print q_value
        return b_value - floor(b_value)
            
    def Q(self, element_dict_by_p):
        """
        Evaluates the local quadratic (defined mod 1) form of an element of the underlying Jordan decomposition.
        The element is expected to be a dictionary with prime keys.

        INPUT:
            `element_dict_by_p` -- a dictionary with prime keys and tuple values {p : tuple}

        OUTPUT:
            a rational number in [0,1)
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]
            sage: L.Q({2 : (0,0,0,0,0), 3 : (0,0,0)})
            0
            sage: L.Q({2 : (0,0,0,0,0), 3 : (0,0,1/3)})
            1/3
            sage: L.Q({2 : (0,0,0,0,0), 3 : (0,0,2/3)})
            1/3
            sage: L.Q({2 : (0,0,1/2,0,0), 3 : (0,0,0)})
            0
            sage: L.Q({2 : (0,0,1/2,1/2,0), 3 : (0,0,0)})
            1/2
            sage: L.Q({2 : (0,0,1/2,1/2,0), 3 : (0,0,1/3)})
            5/6
            sage: L.Q({2 : (0,0,1/2,1/2,1/2), 3 : (0,0,1/3)})
            1/3

        """
        q_value = sum(self.local_Q_p(element_dict_by_p[p], p) for p in self.primes())
        return q_value - floor(q_value)

    def B(self, element_dict_by_p, other_element_dict_by_p):
        """
        Evaluates the bilinear form (defined mod 1) form on elements of the underlying Jordan decomposition.
        The elements are expected to be a dictionary with prime keys.

        INPUT:
            `element_dict_by_p` -- a dictionary with prime keys and tuple values {p : tuple}

            `other_element_dict_by_p` -- a dictionary with prime keys and tuple values {p : tuple}

        OUTPUT:
            a rational number in [0,1)
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]
            sage: el0 = {2 : (0,0,0,0,0), 3 : (0,0,0)}
            sage: el1 = {2 : (0,0,0,0,0), 3 : (0,0,1/3)}
            sage: el2 = {2 : (0,0,1/2,1/2,0), 3 : (0,0,0)}
            sage: L.B(el0,el0)
            0
            sage: L.B(el0,el1)
            0
            sage: L.B(el0,el2)
            0
            sage: L.B(el1,el1)
            2/3
            sage: L.B(el1,el2)
            0
            sage: L.B(el2,el2)
            0
        
        """
        b_value = sum(self.local_B_p(element_dict_by_p[p], other_element_dict_by_p[p], p) for p in self.primes())
        return b_value - floor(b_value)

    @cached_method
    def group_structure(self, p):
        """
        Returns the group sturcture of the p-part of the underlying Jordan decomposition
        
        INPUT:
            `p` -- a prime
        
        OUTPUT:
            a list
    
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 0  1  0  0  0]
            [ 1  0  0  0  0]
            [ 0  0  0  2  0]
            [ 0  0  2  0  0]
            [ 0  0  0  0 12]
            sage: L.local_normal_form(3)

            [-2  0  0]
            [ 0  4  0]
            [ 0  0  6]
            sage: L.group_structure(2)
            [1, 1, 2, 2, 4]
            sage: L.group_structure(3)
            [1, 1, 3]

        """
        result = []
        for q in sorted([q for q in self.__jd.keys() if q % p == 0]):
            result += self.__jd[q][2] * [q]
        if (self.signature() + len(result)) % 2 != 0:
            result = 3 *[Integer(1)] + result
        else:
            result = 2 *[Integer(1)] + result
        return result

    @cached_method
    def sort_2_adic(self):
        """
        Returns a list containing three lists. 
        The first of these contains the indices of the indices belonging to odd 2-adic blocks in the 2-adic local normal form,
        the second list are indices of even 2-adic blocks of type I and the third list are indeces of even 2-adic blocks of type II.
        
        OUTPUT:
            list
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.8^-2.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.local_normal_form(2)

            [ 2  1  0  0  0  0  0]
            [ 1  2  0  0  0  0  0]
            [ 0  0  0  2  0  0  0]
            [ 0  0  2  0  0  0  0]
            [ 0  0  0  0 12  0  0]
            [ 0  0  0  0  0 16  8]
            [ 0  0  0  0  0  8 16]
            sage: L.sort_2_adic()
            [[4], [2, 3], [0, 1, 5, 6]]

        """
        Q_loc = self.local_normal_form(2)
        n = Q_loc.ncols()
        even_I = [j for j in range(n) if Q_loc[j,j] == 0]
        even_II = sorted([j for j in range(n-1) if Q_loc[j,j+1] != 0 and not j in even_I] + [j for j in range(1, n) if Q_loc[j,j-1] != 0 and not j in even_I])
        odds = [j for j in range(n) if not j in (even_I + even_II)]
        return [odds, even_I, even_II]

    def discriminant_form_iterator(self):
        """
        Returns an iterator for representatives of the underlying Jordan decomposition.

        OUTPUT:

            iterator
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: sorted([[(p, el._mu_p(p)) for p in L.primes()] for el in L.discriminant_form_iterator()])

            [[(2, (0, 0, 0)), (3, (0, 0, 0))],
             [(2, (0, 0, 0)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 0)), (3, (0, 0, 2/3))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 2/3))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 2/3))],
             [(2, (0, 0, 3/4)), (3, (0, 0, 0))],
             [(2, (0, 0, 3/4)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 3/4)), (3, (0, 0, 2/3))]]

        """
        S = self.primes()
        d_p = [self.group_structure(p) for p in S]
        it1 = itertools.product(*[itertools.product(*[range(d_p[k][j]) for j in range(len(d_p[k]))]) for k in range(len(S))])
        it2 = itertools.imap(lambda x: {S[k] : tuple([x[k][j]/d_p[k][j] for j in range(len(d_p[k]))]) for k in range(len(S))}, it1)
        it3 = itertools.imap(lambda x: LocalSpaceByJordanDataElement(self, x), it2)
        return it3

    def discriminant_form_reduced(self):
        """
        Returns a list of the elements modulo {-1,+1} in the underlying Jordan decomposition.

        OUTPUT:
            list
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: sorted([[(p, el._mu_p(p)) for p in L.primes()] for el in L.discriminant_form_reduced()])

            [[(2, (0, 0, 0)), (3, (0, 0, 0))],
             [(2, (0, 0, 0)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 2/3))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 1/3))]]

        """
        old_elts = []
        result = []
        for el in self.discriminant_form_iterator():
            if el in old_elts or -el in old_elts:
                continue
            old_elts += [el]
            result += [el]
        return result        
        
    def discriminant_form_iterator_p(self, p):
        """
        Returns an iterator for representatives of p-part of the underlying Jordan decomposition.
        
        INPUT:
            `p` -- a prime
        
        OUTPUT:

            iterator
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: sorted([[(p, el._mu_p(p)) for p in L.primes()] for el in L.discriminant_form_iterator_p(2)])

            [[(2, (0, 0, 0)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/4)), (3, (0, 0, 0))],
             [(2, (0, 0, 1/2)), (3, (0, 0, 0))],
             [(2, (0, 0, 3/4)), (3, (0, 0, 0))]]
            sage: sorted([[(p, el._mu_p(p)) for p in L.primes()] for el in L.discriminant_form_iterator_p(3)])

            [[(2, (0, 0, 0)), (3, (0, 0, 0))],
             [(2, (0, 0, 0)), (3, (0, 0, 1/3))],
             [(2, (0, 0, 0)), (3, (0, 0, 2/3))]]

        """
        S = self.primes()
        d_p = [self.group_structure(pp) for pp in S]
        for j in range(len(S)):
            if S[j] != p:
                d_p[j] = [1 for k in range(len(d_p[j]))]
        it1 = itertools.product(*[itertools.product(*[range(d_p[k][j]) for j in range(len(d_p[k]))]) for k in range(len(S))])
        it2 = itertools.imap(lambda x: {S[k] : tuple([x[k][j]/d_p[k][j] for j in range(len(d_p[k]))]) for k in range(len(S))}, it1)
        it3 = itertools.imap(lambda x: LocalSpaceByJordanDataElement(self, x), it2)
        return it3

    def eisenstein_series(self, weight, prec = 10):
        """
        Return the vector valued Eisenstein series of weight `l` for the underlying finite quadratic module and the Weil representation.

        INPUT:
            `l` -- a half integer, the weight of the Eisenstein series

            `prec` -- the precision to which the Eisenstein series will be computed (default: 10)

        OUTPUT:
            a dicionary of dictionaries
        
        EXAMPLES::
      
            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule(matrix(2,2,[0,1,1,0]))
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {})
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

            sage: F = FiniteQuadraticModule(matrix(2,2,[2,1,1,2]))
            sage: J = F.jordan_decomposition()
            sage: J.genus_symbol()
            '3^-1'
            sage: F = FiniteQuadraticModule('3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.eisenstein_series(5, prec = 10)

            {((3, (0, 0, 0, 0)),): {0: 1,
              1: 246,
              2: 3600,
              3: 19686,
              4: 59286,
              5: 149760,
              6: 295200,
              7: 590892,
              8: 925200,
              9: 1594326},
             ((3, (0, 0, 0, 1/3)),): {1/3: 3,
              4/3: 723,
              7/3: 7206,
              10/3: 28080,
              13/3: 85686,
              16/3: 185043,
              19/3: 390966,
              22/3: 658800,
              25/3: 1170003,
              28/3: 1736646},
             ((3, (0, 0, 0, 2/3)),): {1/3: 3,
              4/3: 723,
              7/3: 7206,
              10/3: 28080,
              13/3: 85686,
              16/3: 185043,
              19/3: 390966,
              22/3: 658800,
              25/3: 1170003,
              28/3: 1736646}}

        """
        return {el.tuple() : el.eisenstein_series(weight, prec=prec) for el in self.discriminant_form_iterator()}

    def small_coefficients(self, n, N):
        """
        The coefficients of the Eisenstein series which are small enough with
        respect to the search of Borcherds products of singular weight.
        """
        return {el.tuple() : el.small_coefficients(n, N) for el in self.discriminant_form_iterator()}

    def orbit_representatives_and_lengths(self, p):
        """
        Returns a dictionary of the form {orbit description : [orbit representative, orbit length]}
        for the p-part of the underlying finite quadratic module with respect to the orthogonal group.
        The orbit description is (order=p^{k+1}, multiplicities v_1,...,v_k, reduced norms t_1,...,t_k).
        
        INPUT:
            `p` -- an odd prime

        OUTPUT:

            dictionary
        
        EXAMPLES::

            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.orbit_representatives_and_lengths(3)

            {(1,): [{2: (0, 0, 0), 3: (0, 0, 0)}, 1],
             (3, 1, 1/3): [{2: (0, 0, 0), 3: (0, 0, 1/3)}, 2]}

        """
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
        """
        Returns a dictionary of the form
        
            {whittaker polynomials : [representative, number of elements with the same whittaker polynomials]}
        
        for the p-part of the underlying finite quadratic module with respect to the orthogonal group.
        For an odd prime p, these invariants can be used to describe orbits with respect to the orthogonal group
        of the p-part of the underlying Jordan decomposition.
        
        INPUT:
            `p` -- a prime

        OUTPUT:

            dictionary
        
        EXAMPLES::

            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1.9^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.whittaker_representatives_and_lengths(2)

            {(): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 0)}, 1],
             ((1, (2, (0, 1), (1, 1))),): [{2: (0, 0, 0, 1/2, 1/2), 3: (0, 0, 0, 0, 0)},
              3],
             ((1, (2, (1/2, 1), (3/2, 1))),): [{2: (0, 0, 0, 1/2, 0), 3: (0, 0, 0, 0, 0)},
              3],
             ((1,
               (2,
                (1/2, -1/2*X + 1),
                (3/2, 1/4*X^2 + 1/2*X + 1),
                (5/2, -1/2*X + 1),
                (7/2,
                 -1/4*X^2 + 1/2*X + 1))),): [{2: (0, 0, 0, 0, 1/2), 3: (0, 0, 0, 0, 0)},
              1],
             ((1, (4, (3/8, 1), (11/8, 1))),
              (2,
               (2,
                (1/2, -1/2*X + 1),
                (3/2, 1/4*X^2 + 1/2*X + 1),
                (5/2, -1/2*X + 1),
                (7/2,
                 -1/4*X^2 + 1/2*X + 1)))): [{2: (0, 0, 0, 1/2, 1/4), 3: (0, 0, 0, 0, 0)},
              6],
             ((1, (4, (7/8, 1), (15/8, 1))),
              (2,
               (2,
                (1/2, -1/2*X + 1),
                (3/2, 1/4*X^2 + 1/2*X + 1),
                (5/2, -1/2*X + 1),
                (7/2,
                 -1/4*X^2 + 1/2*X + 1)))): [{2: (0, 0, 0, 0, 1/4), 3: (0, 0, 0, 0, 0)},
              2]}
            sage: L.whittaker_representatives_and_lengths(3)

            {(): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 0)}, 1],
             ((1,
               (3,
                (0, -1/3*X + 1),
                (1, 1/3*X + 1),
                (2, 1))),): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 1/3)},
              2],
             ((1, (3, (1/3, 1))),): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 1/3, 0)}, 6],
             ((1, (9, (2/9, 1))),
              (3,
               (3,
                (0, -1/3*X + 1),
                (1, 1/3*X + 1),
                (2, 1)))): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 1/9)}, 6],
             ((1, (9, (5/9, 1))),
              (3,
               (3,
                (0, -1/3*X + 1),
                (1, 1/3*X + 1),
                (2, 1)))): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 4/9)}, 6],
             ((1, (9, (8/9, 1))),
              (3,
               (3,
                (0, -1/3*X + 1),
                (1, 1/3*X + 1),
                (2, 1)))): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 2/9)}, 6]}
            sage: L.orbit_representatives_and_lengths(3)

            {(1,): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 0)}, 1],
             (3, 1, 1/3): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 1/3, 0)}, 6],
             (3, 3, 2/3): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 1/3)}, 2],
             (9, 1, 1, 2/9, 2/3): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 1/9)}, 6],
             (9, 1, 1, 5/9, 2/3): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 4/9)}, 6],
             (9, 1, 1, 8/9, 2/3): [{2: (0, 0, 0, 0, 0), 3: (0, 0, 0, 0, 2/9)}, 6]}

        """
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

#    def whittaker_orbit_lengths(self):
#        S = self.primes()
#        p_orbs = {p : self.whittaker_representatives_and_lengths(p) for p in S}
#        result = []
#        for orbs in itertools.product(*[p_orbs[p].keys() for p in S]):
#            #print orbs
#            #for j in range(len(S)):
#            #    print S[j]
#            #    print p_orbs[S[j]]
#            #    print p_orbs[S[j]][orbs[j]]
#            #    print p_orbs[S[j]][orbs[j]][1]
#            result += [prod([p_orbs[S[j]][orbs[j]][1] for j in range(len(S))])]
#        return result
                
class LocalSpaceByJordanDataElement(SageObject):
    r"""
    This class mimics the behaviour of elements in the rational space containing a lattice by providing local data.

    INPUT:

    The constructor may be called in the following way:

    #. ``LocalSpaceByJordanDataElement(parent , entries_as_dict_by_p)``, where

       - `parent` -- an instance of LocalSpaceByJordanData

       - `entries_as_dict_by_p` -- a dictionary of the form {p : tuple} such that this gives an element of the Jordan decomposition of parent

    EXAMPLES::

        sage: from finite_quadratic_module import FiniteQuadraticModule
        sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
        sage: J = F.jordan_decomposition()
        sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
        sage: L.group_structure(2)
        [1, 1, 4]
        sage: L.group_structure(3)
        [1, 1, 3]
        sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
        sage: el
        {2: (0, 0, 1/4), 3: (0, 0, 1/3)}
        sage: el.eisenstein_series(5/2, prec = 10)

        {17/24: 12,
         41/24: 48,
         65/24: 96,
         89/24: 156,
         113/24: 216,
         137/24: 288,
         161/24: 384,
         185/24: 456,
         209/24: 564,
         233/24: 636}

    """
    def __init__(self, parent, entries_as_dict_by_p):
        self._entries = entries_as_dict_by_p
        self._parent = parent
        assert sorted(self._entries.keys()) == sorted(self._parent.primes())

    def _repr_(self):
        return repr(self._entries)
        
    def __eq__(self, other):
        if other == 0:
            return all(all(j == 0 for j in self._entries[q]) for q in self._entries.keys())
        if not isinstance(other,type(self)):
            return False
        return self._parent == other._parent and self._entries == other._entries

    @cached_method
    def tuple(self):
        """
        Returns a tuple representation of the entries.
        
        OUTPUT:

            tuple
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el.tuple()
            ((2, (0, 0, 1/4)), (3, (0, 0, 1/3)))

        """
        return tuple((p, tuple(self._entries[p])) for p in sorted(self._entries.keys()))

    def _cache_key(self):
        return self.tuple()

    def scale(self, p, fac):
        """
        Returns an element with the entries of self, where the p-part is multiplied with fac.

        INPUT:

            `p` - a prime

            `fac` - a rational

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el
            {2: (0, 0, 1/4), 3: (0, 0, 1/3)}
            sage: el.scale(2,2)
            {2: (0, 0, 1/2), 3: (0, 0, 1/3)}
            sage: el
            {2: (0, 0, 1/4), 3: (0, 0, 1/3)}
            sage: el.scale(2,1/2)
            {2: (0, 0, 1/8), 3: (0, 0, 1/3)}

        """
        entries = {p : tuple(self._entries[p]) for p in self._entries.keys()}
        entries[p] = tuple([frac(fac * j) for j in self._entries[p]])
        return LocalSpaceByJordanDataElement(self._parent, entries)
        
    def _neg_(self):
        return -1 * self

    def _add_(self, other):
        entries = {}
        for p in self._entries.keys():
            entries[p] = tuple([frac(other._entries[p][j] + self._entries[p][j]) for j in range(len(self._entries[p]))])
        return LocalSpaceByJordanDataElement(self._parent, entries)

    def __sub__(self, other):
        return self._add_(-1 * other)
        
    def __lmul__(self, other):
        entries = {p : tuple(self._entries[p]) for p in self._entries.keys()}
        for p in self._entries.keys():
            entries[p] = tuple([frac(other * j) for j in self._entries[p]])
        return LocalSpaceByJordanDataElement(self._parent, entries)

    def __rmul__(self, other):
        return self.__lmul__(other)

    def __neg__(self):
        return self._neg_()
    
    def integral_parent(self):
        """
        Returns the LocalSpaceByJordanData with respect to which self is defined.
        """
        return self._parent

    @cached_method
    def Q(self):
        """
        Returns the quadratic form of self (which is defined mod 1).

        OUTPUT:

            a rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,0)})
            sage: el.Q()
            0
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,0)})
            sage: el.Q()
            1/2
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,1/3)})
            sage: el.Q()
            1/3
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,1/3)})
            sage: el.Q()
            5/6

        """
        return self.integral_parent().Q(self._entries)

    @cached_method
    def B(self, other):
        """
        Evaluates the bilinear form (which is defined mod 1) on self and other.

        OUTPUT:

            a rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el0 = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,0)})
            sage: el1 = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,0)})
            sage: el2 = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,0)})
            sage: el3 = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,1/3)})
            sage: el0.B(el0)
            0
            sage: el0.B(el1)
            0
            sage: el0.B(el2)
            0
            sage: el0.B(el3)
            0
            sage: el1.B(el1)
            0
            sage: el1.B(el2)
            1/2
            sage: el1.B(el3)
            0
            sage: el2.B(el2)
            3/4
            sage: el2.B(el3)
            0
            sage: el3.B(el3)
            2/3

        """
        return self.integral_parent().B(self._entries, other._entries)

    def local_Q_p(self, p):
        """
        Returns the local quadratic form of the p-part of self (which is defined mod 1).

        OUTPUT:

            a rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,0)})
            sage: el.local_Q_p(2)
            0
            sage: el.local_Q_p(3)
            0
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el.local_Q_p(2)
            3/8
            sage: el.local_Q_p(3)
            1/3

        """
        return self.integral_parent().local_Q_p(self._entries[p], p)

    def norm(self):
        """
        Returns the quadratic form of self (which is defined mod 1).

        OUTPUT:

            a rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,0)})
            sage: el.norm()
            0
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,0)})
            sage: el.norm()
            1/2
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0), 3 : (0,0,1/3)})
            sage: el.norm()
            1/3
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,1/3)})
            sage: el.norm()
            5/6

        """
        return self.Q()

    def order_p(self, p):
        """
        Returns the order of self (as a group element) in the p-adic part of the Jordan component with respect to which this element is defined.

        OUTPUT:

            a rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el.order_p(2)
            4
            sage: el.order_p(3)
            3
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2), 3 : (0,0,0)})
            sage: el.order_p(2)
            2
            sage: el.order_p(3)
            1

        """
        return max(j.denominator() for j in self._mu_p(p))

    @cached_method
    def multiplicity_reduced_norm_p(self, p, k, allow_2 = False):
        """
        Returns the multiplicity and reduced norm of the p-part of p**k * self.
        (For odd p, these values are invariants w.r.t. the action of the orthogonal group of the underlying finite quadratic module.)        

        INPUT:
            `p` - a prime

            `k` - a nonnegative integer
        
        OUTPUT:

            integer, rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('3^1.9^-1.27^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.group_structure(3)
            [1, 1, 1, 3, 9, 27]
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,1/3,0,1/9)})
            sage: el.multiplicity_reduced_norm_p(3,0)
            (1, 1/3)
            sage: el.multiplicity_reduced_norm_p(3,1)
            (3, 2/3)

        """
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
        """
        Returns the multiplicity of p**k * self.
        (For odd p, these values are invariants w.r.t. the action of the orthogonal group of the underlying finite quadratic module.)
        
        INPUT:
            `p` - a prime

            `k` - a nonnegative integer
        
        OUTPUT:

            integer
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('3^1.9^-1.27^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,1/3,0,1/9)})
            sage: el.multiplicity_p(3,0)
            1
            sage: el.multiplicity_p(3,1)
            3

        """
        return self.multiplicity_reduced_norm_p(p, k, allow_2 = True)[0]

    def reduced_norm_p(self, p, k = 0):
        """
        Returns the reduced norm of p**k * self (not well defined for p=2).
        (For odd p, these values are invariants w.r.t. the action of the orthogonal group of the underlying finite quadratic module.)
        

        INPUT:
            `p` - a prime

            `k` - a nonnegative integer
        
        OUTPUT:

            rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('3^1.9^-1.27^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,1/3,0,1/9)})
            sage: el.reduced_norm_p(3,0)
            1/3
            sage: el.reduced_norm_p(3,1)
            2/3

        """
        return self.multiplicity_reduced_norm_p(p, k, allow_2 = False)[1]        

    def orbit_p(self, p):
        """
        Returns the orbit description of the p-part of self with respect to the action of the orthogonal group
        of the underlying finite quadratic module.
        The orbit description is (order=p^{k+1}, multiplicities v_1,...,v_k, reduced norms t_1,...,t_k).
        
        INPUT:
            `p` -- an odd prime

        OUTPUT:

            tuple
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('3^1.9^-1.27^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,1/3,0,1/9)})
            sage: el.orbit_p(3)
            (9, 1, 3, 1/3, 2/3)

        """
        assert p > 2
        maxk = self.order_p(p).valuation(p)
        orb = [p**maxk]
        orb += [self.multiplicity_p(p, k) for k in range(maxk)]
        orb += [self.reduced_norm_p(p, k) for k in range(maxk)]
        orb = tuple(orb)
        return orb

    @cached_method
    def order(self):
        """
        Returns the order of self as a group element in the underlying finite quadratic module.

        OUTPUT:

            integer
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('3^1.9^-1.27^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (1/3,0,1/9)})
            sage: el.order()
            9

            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el.order()
            12

        """
        return prod(self.order_p(p) for p in self.integral_parent().primes())

    @cached_method
    def _mu_p(self, p):
        """
        Returns the local coordinates in the p-part of the Jordan decomposition

        INPUT:
            `p` -- a prime
        
        OUTPUT:

            tuple
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el._mu_p(2)
            (0, 0, 1/4)
            sage: el._mu_p(3)
            (0, 0, 1/3)

        """
        if p in self.integral_parent().primes():
            return self._entries[p]
        else:
            return tuple([0 for j in range(self.integral_parent().local_normal_form(p).ncols())])

    def _mu_p_i(self, p, i):
        """
        Returns the local coordinates in the p-part of the Jordan decomposition

        INPUT:
            `p` -- a prime

            `i` -- a nonnegative integer
        
        OUTPUT:

            rational
        
        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/4), 3 : (0,0,1/3)})
            sage: el._mu_p_i(3,0)
            0
            sage: el._mu_p_i(3,1)
            0
            sage: el._mu_p_i(3,2)
            1/3
            sage: el._mu_p_i(2,0)
            0
            sage: el._mu_p_i(2,1)
            0
            sage: el._mu_p_i(2,2)
            1/4

        """
        return self._entries[p][i]

    @cached_method
    def H(self, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        If p != 2, returns the list `H` of coordinates that are p-adic integers.
        If p == 2, returns a ditcionary with keys 'H', 'M' and 'N' pointing to the corresponding lists
        for odd, type I and type II components.
        These lists are computed for the coordinates of self corresponding to the normalized local
        form for the prime `p`.

        INPUT:
            `p` -- a positive prime number

        OUTPUT:
            a list or a dictionary containing three lists.

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.group_structure(2)
            [1, 1, 2, 2, 4]
            sage: L.group_structure(3)
            [1, 1, 3]
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0), 3 : (0,0,0)})
            sage: el.H(2)
            {'H': [4], 'M': [0, 2], 'N': []}
            sage: el.H(3)
            [0, 1, 2]
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,1/2,1/4), 3 : (0,0,1/3)})
            sage: el.H(2)
            {'H': [], 'M': [0], 'N': []}
            sage: el.H(3)
            [0, 1]

        """
        if p==2:
            [odds, even_I, even_II] = self.integral_parent().sort_2_adic()
            Hs = [j for j in odds if self._mu_p_i(p, j).valuation(p) >= 0]
            Ms = [j for j in even_I[0::2] if self._mu_p_i(p, j).valuation(p) >= 0 and self._mu_p_i(p, j+1).valuation(p) >= 0]
            Ns = [j for j in even_II[0::2] if self._mu_p_i(p, j).valuation(p) >= 0 and self._mu_p_i(p, j+1).valuation(p) >= 0]
            return {'H':Hs, 'M':Ms, 'N':Ns}
        else:
            return [i for i in range(len(self._mu_p(p))) if self._mu_p_i(p, i).valuation(p) >= 0]

    @cached_method
    def L(self, k, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        This list is computed for the coordinates of self corresponding to the normalized local
        form for the prime `p`.

        INPUT:
            `k` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            a list.

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0), 3 : (0,0,0)})
            sage: el.L(0,2)
            []
            sage: el.L(1,2)
            []
            sage: el.L(2,2)
            []
            sage: el.L(3,2)
            [4]
            sage: el.L(4,2)
            []
            sage: el.L(5,2)
            [4]
            sage: el.L(0,3)
            []
            sage: el.L(1,3)
            [0, 1]
            sage: el.L(2,3)
            [2]
            sage: el.L(3,3)
            [0, 1]
            sage: el.L(4,3)
            [2]
            sage: el.L(5,3)
            [0, 1]

        """
        if p==2:
            return [i for i in self.H(p)['H']
                    if (self.integral_parent().valuation(i,p)-k) < 0 and is_odd(self.integral_parent().valuation(i,p)-k)]
        else:
            return [i for i in self.H(p)
                    if (self.integral_parent().valuation(i,p)-k) < 0 and is_odd(self.integral_parent().valuation(i,p)-k)]
        
    def l(self, k, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        Returns the length of the list self.L(k, p).

        INPUT:
            `k` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            a non-negative integer

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0), 3 : (0,0,0)})
            sage: el.l(0,2)
            0
            sage: el.l(1,2)
            0
            sage: el.l(2,2)
            0
            sage: el.l(3,2)
            1
            sage: el.l(4,2)
            0
            sage: el.l(5,2)
            1
            sage: el.l(0,3)
            0
            sage: el.l(1,3)
            2
            sage: el.l(2,3)
            1
            sage: el.l(3,3)
            2
            sage: el.l(4,3)
            1
            sage: el.l(5,3)
            2

        """
        return len(self.L(k,p))

    @cached_method
    def d(self, k, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.

        INPUT:
            `k` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            a half-integer

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0), 3 : (0,0,0)})
            sage: el.d(0,2)
            0
            sage: el.d(1,2)
            0
            sage: el.d(3,2)
            -5/2
            sage: el.d(4,2)
            -4
            sage: el.d(5,2)
            -11/2
            sage: el.d(0,3)
            0
            sage: el.d(1,3)
            0
            sage: el.d(2,3)
            -1/2
            sage: el.d(3,3)
            -1
            sage: el.d(4,3)
            -3/2
            sage: el.d(5,3)
            -2

        """
        if p==2:
            return (k
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['H']])/Integer(2)
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['M']])
                    + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)['N']]))
        else:
            return k + sum([min([self.integral_parent().valuation(i,p)-k,0]) for i in self.H(p)])/Integer(2)

    @cached_method
    def eps(self, k, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        Returns -1 or 1 if p != 2 and an integer otherwise.

        INPUT:
            `k` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            an integer

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,1/2,1/4), 3 : (0,0,1/3)})
            sage: el.eps(0,2)
            1
            sage: el.eps(1,2)
            1
            sage: el.eps(2,2)
            1
            sage: el.eps(3,2)
            1
            sage: el.eps(0,3)
            1
            sage: el.eps(1,3)
            -1
            sage: el.eps(2,3)
            1
            sage: el.eps(3,3)
            -1
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,1/2,0), 3 : (0,0,0)})
            sage: el.eps(0,2)
            1
            sage: el.eps(1,2)
            1
            sage: el.eps(2,2)
            1
            sage: el.eps(3,2)
            3
            sage: el.eps(0,3)
            1
            sage: el.eps(1,3)
            -1
            sage: el.eps(2,3)
            1
            sage: el.eps(3,3)
            -1

        """
        if p==2:
            return prod([self.integral_parent().unit(j, p) for j in self.L(k, p)])
        else:
            return ((self.modified_hilbert_symbol(-1,p)**floor((self.l(k,p)/Integer(2))))
                    * prod([self.modified_hilbert_symbol(self.integral_parent().unit(i,p),p) for i in self.L(k,p)]))

    @cached_method
    def K0(self, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.

        INPUT:
            `p` -- a positive prime number

        OUTPUT:
            an integer

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^2.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0), 3 : (0,0,0)})
            sage: el.K0(2)
            +Infinity
            sage: el.K0(3)
            +Infinity
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,0,0), 3 : (0,0,1/3)})
            sage: el.K0(2)
            0
            sage: el.K0(3)
            0
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,1/4), 3 : (0,0,1)})
            sage: el.K0(2)
            0
            sage: el.K0(3)
            +Infinity
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,1/2), 3 : (0,0,1)})
            sage: el.K0(2)
            2
            sage: el.K0(3)
            +Infinity

        """
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
    @cached_method
    def p(self, k):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        This invariant is only used in the 2-adic case and equals -1 or 1.

        INPUT:
            `k` -- an integer

        OUTPUT:
            -1 or 1

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^-4.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.group_structure(2)
            [1, 1, 2, 2, 2, 2, 4]
            sage: L.group_structure(3)
            [1, 1, 3]
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,1/2,1/2,1/2,1/2), 3 : (0,0,1/3)})
            sage: el.p(0)
            1
            sage: el.p(1)
            -1
            sage: el.p(2)
            1
            sage: el.p(3)
            -1
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0,0,0), 3 : (0,0,0)})
            sage: el.p(0)
            1
            sage: el.p(1)
            -1
            sage: el.p(2)
            -1
            sage: el.p(3)
            -1

        """
        return Integer(-1)**sum([min([self.integral_parent().valuation(i,2)-k,0]) for i in self.H(2)['N']])

    @cached_method
    def delta(self, k):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        This invariant is only used in the 2-adic case and equals 0 or 1.

        INPUT:
            `k` -- an integer

        OUTPUT:
            0 or 1

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^-4.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0,0,0), 3 : (0,0,0)})
            sage: el.delta(0)
            1
            sage: el.delta(1)
            1
            sage: el.delta(2)
            0
            sage: el.delta(3)
            1
            sage: el.delta(4)
            1
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,1/2,1/2,1/2,1/2,1/2), 3 : (0,0,1/3)})
            sage: el.delta(0)
            1
            sage: el.delta(1)
            1
            sage: el.delta(2)
            1
            sage: el.delta(3)
            1
            sage: el.delta(4)
            1

        """
        for j in self.H(2)['H']:
            if k == self.integral_parent().valuation(j,2):
                return 0
        return 1

    @cached_method
    def modified_hilbert_symbol(self, a, p):
        """
        Returns 0 if a is not a unit in Zp(p), else return the Hilbert symbol (a,p)_p.

        INPUT:
            `a` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            -1, 0 or 1

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^-4.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0,0,0), 3 : (0,0,0)})
            sage: el.modified_hilbert_symbol(0,2)
            0
            sage: el.modified_hilbert_symbol(1,2)
            1
            sage: el.modified_hilbert_symbol(2,2)
            0
            sage: el.modified_hilbert_symbol(3,2)
            -1
            sage: el.modified_hilbert_symbol(4,2)
            0
            sage: el.modified_hilbert_symbol(5,2)
            -1
            sage: el.modified_hilbert_symbol(6,2)
            0
            sage: el.modified_hilbert_symbol(7,2)
            1
            sage: el.modified_hilbert_symbol(0,3)
            0
            sage: el.modified_hilbert_symbol(1,3)
            1
            sage: el.modified_hilbert_symbol(2,3)
            -1
            sage: el.modified_hilbert_symbol(0,5)
            0
            sage: el.modified_hilbert_symbol(1,5)
            1
            sage: el.modified_hilbert_symbol(2,5)
            -1
            sage: el.modified_hilbert_symbol(3,5)
            -1
            sage: el.modified_hilbert_symbol(4,5)
            1

        """
        if Zp(p)(a).is_unit():
            return hilbert_symbol(a,p,p)
        else:
            return 0

    @cached_method
    def f1(self, x, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.

        INPUT:
            `x` -- an integer
        
            `p` -- a positive prime number

        OUTPUT:
            -1/p, -1/sqrt(p) or 1/sqrt(p)

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^-4.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0,0,0), 3 : (0,0,0)})
            sage: el.f1(1 * 3**0, 3)
            -1/3
            sage: el.f1(1 * 3**1, 3)
            1/3*sqrt(3)
            sage: el.f1(2 * 3**1, 3)
            -1/3*sqrt(3)

        """
        a=valuation(x,p)
        if is_even(self.l(a+1,p)):
            return -1/p
        else:
            return self.modified_hilbert_symbol(x * p**-a,p)/sqrt(p)

    @cached_method
    def t(self, m, p):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        Returns `m` minus the quadratic form evaluated at those coordinates of self that are not in the list
        `H`, `M` or `N` (the listst that point to (pairs of) coordinates that are p-adic integers).

        INPUT:
            `m` -- a rational
        
            `p` -- a positive prime number

        OUTPUT:
            a rational

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2^-4.4_3^-1.3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.group_structure(2)
            [1, 1, 2, 2, 2, 2, 4]
            sage: L.group_structure(3)
            [1, 1, 3]
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0,0,1/4), 3 : (0,0,1/3)})
            sage: el.Q()
            17/24
            sage: el.local_Q_p(2)
            3/8
            sage: el.local_Q_p(3)
            1/3
            sage: el.t(3/8,2)
            0
            sage: el.t(3/8+1,2)
            1
            sage: el.t(3/8+2,2)
            2
            sage: el.t(1/3,3)
            0
            sage: el.t(1/3+1,3)
            1
            sage: el.t(1/3+2,3)
            2

        """
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

    @cached_method
    def nu(self, m, k):
        """
        An invariant from [Kudla, Yang - Eisenstein Series for SL(2)].
        Used in the computation of Eisenstein series for the parent lattice and the Weil representation.
        This invariant is only used in the 2-adic case.

        INPUT:
            `m` -- a rational
         
            `k` -- an integer

        OUTPUT:
            a rational

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2_1^1.4_3^-1.8_5^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0,0,0)})
            sage: el.nu(0,0)
            0
            sage: el.nu(0,1)
            0
            sage: el.nu(0,2)
            -1
            sage: el.nu(0,3)
            -4
            sage: el.nu(0,4)
            -9
            sage: el.nu(0,5)
            -9

        """
        return (self.t(m, 2) * 2**(Integer(3)-k)
                - sum([self.integral_parent().unit(j,2)
                       for j in self.H(2)['H']
                       if self.integral_parent().valuation(j,2) < k])
                )

    @cached_method
    def Wpoly(self, p, m, verbose=False):
        """
        Returns a polynomial or rational function corresponding to the local Whittaker
        (cnf. local densities) function as described in [Kudla, Yang - Eisenstein Series for SL(2)].
        
        INPUT:
            `p` -- a positive prime number
        
            `m` -- a rational number

        OUTPUT:
            a polynomial or rational function in one variable.

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2_1^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0)})
            sage: el.Wpoly(2,1/2)
            0

            sage: el.Wpoly(2,1)
            1/4*X^3 + 1/4*X^2 + 1
            sage: el.Wpoly(2,2)
            -1/4*X^2 + 1
            sage: el.Wpoly(2,3)
            -1/4*X^2 + 1
            sage: el.Wpoly(2,4)
            1/8*X^5 + 1/8*X^4 + 1/4*X^2 + 1
            sage: el.Wpoly(2,5)
            -1/4*X^3 + 1/4*X^2 + 1
            sage: el.Wpoly(2,6)
            -1/4*X^2 + 1

            sage: F = FiniteQuadraticModule('3^-1.9^-1.27^-1.81^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,0,0,0)})
            sage: el.Wpoly(3,1)
            -1/3*X + 1
            sage: el.Wpoly(3,2)
            -1/3*X + 1
            sage: el.Wpoly(3,3)
            1/3*X^2 + 2/3*X + 1
            sage: el.Wpoly(3,4)
            -1/3*X + 1
            sage: el.Wpoly(3,5)
            -1/3*X + 1
            sage: el.Wpoly(3,6)
            -1/3*X^2 + 2/3*X + 1
            sage: el.Wpoly(3,7)
            -1/3*X + 1
            sage: el.Wpoly(3,8)
            -1/3*X + 1
            sage: el.Wpoly(3,9)
            1/9*X^3 + 2/3*X + 1

        """
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
        """
        Evaluates the local Whittaker (cnf. local densities) function as described in
        [Kudla, Yang - Eisenstein Series for SL(2)] at p**-s.
        
        INPUT:
            `p` -- a positive prime number
        
            `m` -- a rational number

            `s` -- an integer, a rational or a complex number

        OUTPUT:
            a number (mostly complex or rational, depending on the input)

        EXAMPLES::

            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule('2_1^1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {2 : (0,0,0)})
            sage: el.W(2,1/2,3)
            0

            sage: el.W(2,1,3)
            2057/2048
            sage: el.W(2,2,3)
            255/256
            sage: el.W(2,3,3)
            255/256
            sage: el.W(2,4,3)
            263177/262144
            sage: el.W(2,5,3)
            2055/2048
            sage: el.W(2,6,3)
            255/256

            sage: F = FiniteQuadraticModule('3^-1.9^-1.27^-1.81^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,0,0,1/3)})
            sage: el.W(3,1,7)
            6560/6561
            sage: el.W(3,2,7)
            6560/6561
            sage: el.W(3,3,7)
            14353282/14348907
            sage: el.W(3,4,7)
            6560/6561
            sage: el.W(3,5,7)
            6560/6561
            sage: el.W(3,6,7)
            14353280/14348907
            sage: el.W(3,7,7)
            6560/6561
            sage: el.W(3,8,7)
            6560/6561
            sage: el.W(3,9,7)
            6563/6561

        """
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
        """
        Returns a touple of touples containing p**self.K0(p) Whittaker polynomials.
        These can be used as invariants of elements under the action of the orthogonal group.
        This function is expensive, but can be usefull for research purposes.
        """
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
        """
        Returns touples of touples of touples containing enought Whittaker polynomials.
        These can be used as invariants of elements under the action of the orthogonal group.
        If p is an odd prime, there is exactly one orbit with these discriminants.
        For p=2, we do not know if this still holds.
        This function is expensive, but can be usefull for research purposes.
        """
        return [(p**k, self.scale(p, p**k)._Wpoly_invariants(p)) for k in range(self.order_p(p).valuation(p))]

    def eisenstein_series(self, weight, allow_weight_2 = True, prec=10, verbose=False):
        """
        Return the Eisenstein series associated to self to precision `prec`.
        If L is a lattice that provides the same local data we use here, then this returns the Eisenstein series
        associated to the characteristic function of self + L. This is part of a vector valued Eisenstein series
        of weight `weight` for this lattice and the Weil representation.

        INPUT:
            `weight` -- a half integer, the weight of the Eisenstein series
        
            `prec` -- the precision to which the Eisenstein series will be computed (default: 10)

        OUTPUT:
            a dicionary
        
        EXAMPLES::

            ## Compare with classical Modular Forms
            ## ------------------------------------
            sage: from sage.all import ModularForms

            ## Hyperbolic plane
            ## ----------------        
            sage: from finite_quadratic_module import FiniteQuadraticModule
            sage: F = FiniteQuadraticModule(matrix(2,2,[0,1,1,0]))
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: el = LocalSpaceByJordanDataElement(L, {})
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
            sage: eis  = ModularForms(1,4).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == el.eisenstein_series(4,prec = 100)
            True


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
            sage: eis = ModularForms(1,6).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == L.eisenstein_series(6, prec = 100)[(0,0)]
            True

            sage: L.eisenstein_series(8, prec = 10)
            {(0, 0): {0: 1,
              1: 480,
              2: 61920,
              3: 1050240,
              4: 7926240,
              5: 37500480,
              6: 135480960,
              7: 395301120,
              8: 1014559200,
              9: 2296875360}}
            sage: eis = ModularForms(1,8).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == L.eisenstein_series(8, prec = 100)[(0,0)]
            True

            ## The E8 lattice
            ## --------------
            sage: L = Lattice(matrix(8,8,[2,-1,0,0,0,0,0,0,
            ....: -1,2,-1,0,0,0,0,0,
            ....: 0,-1,2,-1,0,0,0,-1,
            ....: 0,0,-1,2,-1,0,0,0,
            ....: 0,0,0,-1,2,-1,0,0,
            ....: 0,0,0,0,-1,2,-1,0,
            ....: 0,0,0,0,0,-1,2,0,
            ....: 0,0,-1,0,0,0,0,2]))

            sage: L.eisenstein_series(4, prec = 10)
            {(0, 0, 0, 0, 0, 0, 0, 0): {0: 1,
              1: 240,
              2: 2160,
              3: 6720,
              4: 17520,
              5: 30240,
              6: 60480,
              7: 82560,
              8: 140400,
              9: 181680}}
            sage: eis = ModularForms(1,4).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == L.eisenstein_series(4, prec = 100)[(0,0,0,0,0,0,0,0)]
            True

            sage: L.eisenstein_series(6, prec = 10)
            {(0, 0, 0, 0, 0, 0, 0, 0): {0: 1,
            1: -504,
            2: -16632,
            3: -122976,
            4: -532728,
            5: -1575504,
            6: -4058208,
            7: -8471232,
            8: -17047800,
            9: -29883672}}
            sage: eis = ModularForms(1,6).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == L.eisenstein_series(6, prec = 100)[(0,0,0,0,0,0,0,0)]
            True

            sage: L.eisenstein_series(8, prec = 10)
            {(0, 0, 0, 0, 0, 0, 0, 0): {0: 1,
              1: 480,
              2: 61920,
              3: 1050240,
              4: 7926240,
              5: 37500480,
              6: 135480960,
              7: 395301120,
              8: 1014559200,
              9: 2296875360}}
            sage: eis = ModularForms(1,8).eisenstein_series()[0]
            sage: coeffs = eis.coefficients(range(100))
            sage: d = dict((j, coeffs[j] / coeffs[0]) for j in range(100))
            sage: d == L.eisenstein_series(8, prec = 100)[(0,0,0,0,0,0,0,0)]
            True

        ::

            ## The following was confirmed by the Siegel-Weil-Formula after adding an E8-lattice
            ## ---------------------------------------------------------------------------------
            sage: F = FiniteQuadraticModule('3^-1')
            sage: J = F.jordan_decomposition()
            sage: L = LocalSpaceByJordanData(J._jordan_decomposition_data())
            sage: L.group_structure(3)
            [1, 1, 1, 3]
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,0)})
            sage: el.eisenstein_series(5, prec = 5)
            {0: 1, 1: 246, 2: 3600, 3: 19686, 4: 59286}
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,1/3)})
            sage: el.eisenstein_series(5, prec = 5)
            {1/3: 3, 4/3: 723, 7/3: 7206, 10/3: 28080, 13/3: 85686}
            sage: el = LocalSpaceByJordanDataElement(L, {3 : (0,0,0,2/3)})
            sage: el.eisenstein_series(5, prec = 5)
            {1/3: 3, 4/3: 723, 7/3: 7206, 10/3: 28080, 13/3: 85686}
        
        """
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
            if not l.is_integer() or (Integer(-1)**l != kappa.sign()):
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
                    print "p:", p, 
                fac *= parent.weil_index(p) * p**(-parent.det().valuation(p)/Integer(2)) / (1 - p**Integer(1 - 2*l))
                if verbose:
                    print fac
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

    def small_coefficients(self, n, N):
        """
        The coefficients of the Eisenstein series which are small enough with
        respect to the search of Borcherds products of singular weight.
        """
        d = self.integral_parent().det()
        eis_weight = n / Integer(2) + 1
        sing_weight = n / Integer(2) - 1
        C = C_eisenstein_coeff_estimate(eis_weight, d, N)
        bound = n / Integer(2) - 1
        if self.order() in [1,2]:
            bound *= 2
        prec = floor((C**-1 * bound)**(Integer(2)/n) ) + 1

        eis = self.eisenstein_series(eis_weight, prec = prec)
        result = dict()
        #b = False

        for k in eis.keys():
            if -eis[k] <= bound:
                result[k] = eis[k]
                #b = True

        if self.order() == 1:
            del result[0]

        return result

def C_eisenstein_coeff_estimate(k, d, N):
    """
    A constand used to estimate the non zero coefficients of Eisenstein series of weight k
    for a lattice of determinant d splitting a scaled hyperbolic plane H(N)."""
    m = Integer(2)*k
    assert m in ZZ
    result = Integer(2)**(k+1) * pi**k / sqrt(abs(d)) / gamma__exact(k)
    if is_even(m):
        result *= (Integer(2)-zeta(k-1)) / zeta(k)
        for p in (Integer(2)*d).prime_divisors():
            result *= p**((3-Integer(2)*k)*valuation(N,p)) * (1-p**Integer(-1))
    else:
        result *= (Integer(2)-zeta(k-1/Integer(2))) / zeta(k-1/Integer(2))
        for p in (Integer(2)*d).prime_divisors():
            result *= p**((3-Integer(2)*k)*valuation(N,p)) * (1-p**Integer(-1)) / (1-p**(1-Integer(2)*k))
    return result / Integer(2) # Here we need the factor 1/2 due to different normalizations in Bruinier-Kuss and Kudla-Yang

