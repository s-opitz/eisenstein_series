"""
Tools to compute with finite quadratic modules and simple lattices.

AUTHORS: 
- Stephan Ehlen (implementation of Genus Symbol, 2014)
- Sebastian Opitz (code to compute orbits and representation numbers, 2014)
- a few code snippets have been copied from the FiniteQuadraticModule code,
written by Nils Skoruppa et. al., see the psage repository (https://github.com/sehlen/psage)
or http://data.countnumber.de


This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License version 3
as published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.


"""

from sage.all import ZZ, Zmod, sys, parallel, is_prime, colors, cached_function, Integer, Partitions, Set, QQ, RR, is_prime_power, next_prime, prime_range, is_squarefree, uniq, MatrixSpace, kronecker, CC, exp, walltime, RealField, floor, pari, pi, ComplexField, sqrt, text, arrow, is_even, squarefree_part, polygon2d, CyclotomicField, is_odd, is_even, is_prime, cartesian_product, prod, log, gcd, sign, valuation, binomial, inverse_mod, lcm, odd_part
from finite_quadratic_module import FiniteQuadraticModule
#from psage.modform.weilrep_tools.dimension import VectorValuedModularForms
from sage.misc.decorators import options
from sage.misc.flatten import flatten
from sage.misc.latex import LatexExpr
from sage.modular.dims import dimension_cusp_forms
from copy import copy, deepcopy
from sage.parallel.decorate import *
from sage.misc.cachefunc import *
import itertools
#from sfqm.tools import BB, h

class GenusSymbol(object):

    _K = CyclotomicField(8)
    _z = _K.gen()

    def __init__(self, s='1^+1', reduce_symbol=True):
        r"""
         Init a genus symbol with a string of the following form:
         for a prime power $q = p^r$ with $p>2$ and for each integer $n$, there are two possible symbols:
         a) $q^+n$
         b) $q^-n$
         For $p=2$, we accept all symbols of the form $q_t^+n$ and $q_t^-n$,
         such that $t \equiv n \pmod{2}$ and the symbols $q^+n$ as well as $q^-n$
         if $n$ is even. For the meaning of these symbols, we refer to [BEF].

         These symbols can be arbitrarily concatenated.
         They have to be separated by a dot ``.``.

         Note that we do not use any parenthesis for the explnents or subscripts to simplify the notation
         and to be compatible with the FiniteQuadraticModule class.

         Example:
           ```2^-2.4_2^+2.3^-1.27^-3.25^+1``` is a valid symbol.

         EXAMPLES::

           sage: s=GenusSymbol('2^-2.4_2^+2.3^-1.27^-3.25^+1')
           sage: s
           Genus symbol 2^-2.4_2^+2.3^-1.27^-3.25^+1
           sage: s.signature()
           6
           sage: s.level()
           5400
           sage: [s.char_invariant(n) for n in s.level().divisors()]
           [(-zeta8^2, 1/9720),
            (zeta8^2, 1/2430),
            (zeta8^2, 1/1080),
            (0, 0),
            (zeta8^2, 1/1944*sqrt(1/5)),
            (-zeta8^2, 1/270),
            (1, 1/1215),
            (-1, 1/120*sqrt(1/3)),
            (zeta8^2, 1/486*sqrt(1/5)),
            (0, 0),
            (zeta8^2, 1/216*sqrt(1/5)),
            (-1, 1/30*sqrt(1/3)),
            (0, 0),
            (1, 1/135),
            (-zeta8^2, 1/1944),
            (zeta8^2, 1/40),
            (zeta8^2, 1/54*sqrt(1/5)),
            (0, 0),
            (1, 1/243*sqrt(1/5)),
            (-1, 1/24*sqrt(1/15)),
            (zeta8^2, 1/486),
            (-zeta8^2, 1/10),
            (0, 0),
            (zeta8^2, 1/15*sqrt(1/3)),
            (zeta8^2, 1/216),
            (1, 1/6*sqrt(1/15)),
            (0, 0),
            (0, 0),
            (-1, 1/27*sqrt(1/5)),
            (zeta8^2, 1/8*sqrt(1/5)),
            (-zeta8^2, 1/54),
            (0, 0),
            (1, 1/243),
            (1, 1/5),
            (-1, 1/24*sqrt(1/3)),
            (zeta8^2, 1/2*sqrt(1/5)),
            (0, 0),
            (-zeta8^2, 1/3*sqrt(1/15)),
            (-1, 1/6*sqrt(1/3)),
            (0, 0),
            (1, 1/27),
            (zeta8^2, 1/8),
            (0, 0),
            (-1, sqrt(1/5)),
            (-zeta8^2, 1/2),
            (zeta8^2, 1/3*sqrt(1/3)),
            (0, 0),
            (1, 1)]
        """
        if isinstance(s, dict):
            self._symbol_dict = s
            # print "in init: ", s
            if not self._is_valid():
                raise ValueError
        else:
            if s == '' or s == '1' or s == '1^1' or s == '1^+1':
                self._symbol_dict = {}
            else:
                self._from_string(s)
        #self.__reset_sigma = False
        self.__sigma = dict()
        if reduce_symbol:
            self._reduce()
        self._B = dict()

    def canonical_symbol(self):
        raise NotImplementedError

    def defines_isomorphic_module(self, other):
        if isinstance(other, str):
            other = GenusSymbol(other)
        elif not isinstance(other, GenusSymbol):
            raise TypeError
        if self == other:
            return True
        if self.group_structure() != other.group_structure():
            return False
        divs = self.level().divisors()
        for t in divs:
            if self.char_invariant(t) != other.char_invariant(t):
                return False
        return True

    def finite_quadratic_module(self):
        r"""
          Returns the finite quadratic module corresponding to this genus symbol.
        """
        return FiniteQuadraticModule(str(self))

    def p_rank(self, p):
        if not is_prime(p):
            return Integer(0)
        if not self._symbol_dict.has_key(p):
            return Integer(0)
        return sum([s[1] for s in self._symbol_dict[p]])

    def order(self):
        if self._symbol_dict == {}:
            return Integer(1)
        else:
            return Integer(prod([p ** (s[0] * s[1]) for p, l in self._symbol_dict.iteritems() for s in l]))

    @cached_method
    def _ppowers(self, p=None):
        if p == None:
            return sorted([p**a.valuation(p) for p in self.level().prime_divisors() for a in self.jordan_components(p)])
        else:
            return sorted([p**a.valuation(p) for a in self.jordan_components(p)])

    @cached_method
    def group_structure(self):
        l = []
        # print "type(level): ", type(self.level())
        # print self.level().prime_factors()
        for p in self.level().prime_factors():
            # print p, type(p)
            for c in self.jordan_components(p):
                # print c, type(c)
                for r in range(c.p_rank(p)):
                    # print r, c.valuation(p)
                    l.append(p ** c.valuation(p))
        return l

    def orbit_list(self, p = None, short = False):
        r"""
        If this is the Jordan decomposition for $(M,Q)$, return the dictionary of
        dictionaries of orbits corresponding to the p-groups of $M$.
        If a prime p is given only the dictionary of orbits for the p-group is returned. 
        OUTPUT:
            dictionary -- the mapping p --> (dictionary -- the mapping orbit --> the number of elements in this orbit)

        EXAMPLES:
            sage: A = FiniteQuadraticModule('3^-3.25^2')
            sage: J = JordanDecomposition(A)
            sage: J.orbit_list() == \
                  {3: \
                      {(1,): 1, \
                       (3, 1, 0): 8, \
                       (3, 1, 1/3): 6, \
                       (3, 1, 2/3): 12}, \
                   5: {(1,): 1, \
                       (5, 5, 0): 8, \
                       (5, 5, 1/5): 4, \
                       (5, 5, 2/5): 4, \
                       (5, 5, 3/5): 4, \
                       (5, 5, 4/5): 4, \
                       (25, 1, 1, 0, 0): 40, \
                       (25, 1, 1, 1/25, 1/5): 20, \
                       (25, 1, 1, 2/25, 2/5): 20, \
                       (25, 1, 1, 3/25, 3/5): 20, \
                       (25, 1, 1, 4/25, 4/5): 20, \
                       (25, 1, 1, 1/5, 0): 40, \
                       (25, 1, 1, 6/25, 1/5): 20, \
                       (25, 1, 1, 7/25, 2/5): 20, \
                       (25, 1, 1, 8/25, 3/5): 20, \
                       (25, 1, 1, 9/25, 4/5): 20, \
                       (25, 1, 1, 2/5, 0): 40, \
                       (25, 1, 1, 11/25, 1/5): 20, \
                       (25, 1, 1, 12/25, 2/5): 20, \
                       (25, 1, 1, 13/25, 3/5): 20, \
                       (25, 1, 1, 14/25, 4/5): 20, \
                       (25, 1, 1, 3/5, 0): 40, \
                       (25, 1, 1, 16/25, 1/5): 20, \
                       (25, 1, 1, 17/25, 2/5): 20, \
                       (25, 1, 1, 18/25, 3/5): 20, \
                       (25, 1, 1, 19/25, 4/5): 20, \
                       (25, 1, 1, 4/5, 0): 40, \
                       (25, 1, 1, 21/25, 1/5): 20, \
                       (25, 1, 1, 22/25, 2/5): 20, \
                       (25, 1, 1, 23/25, 3/5): 20, \
                       (25, 1, 1, 24/25, 4/5): 20}}
            True
            sage: A = FiniteQuadraticModule('3^-3.27^2')
            sage: J = JordanDecomposition(A)
            sage: J.orbit_list(3) == \
                  {(1,): 1, \
                  (3, 1, 0): 72, \
                  (3, 1, 1/3): 54, \
                  (3, 1, 2/3): 108, \
                  (3, 9, 1/3): 4, \
                  (3, 9, 2/3): 4, \
                  (9, 1, 3, 0, 1/3): 432, \
                  (9, 1, 3, 0, 2/3): 216, \
                  (9, 1, 3, 1/3, 1/3): 288, \
                  (9, 1, 3, 1/3, 2/3): 432, \
                  (9, 1, 3, 2/3, 1/3): 216, \
                  (9, 1, 3, 2/3, 2/3): 288, \
                  (9, 3, 3, 1/9, 1/3): 12, \
                  (9, 3, 3, 2/9, 2/3): 12, \
                  (9, 3, 3, 4/9, 1/3): 12, \
                  (9, 3, 3, 5/9, 2/3): 12, \
                  (9, 3, 3, 7/9, 1/3): 12, \
                  (9, 3, 3, 8/9, 2/3): 12, \
                  (27, 1, 1, 1, 1/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 2/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 4/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 5/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 7/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 8/27, 8/9, 2/3): 972, \
                  (27, 1, 1, 1, 10/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 11/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 13/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 14/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 16/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 17/27, 8/9, 2/3): 972, \
                  (27, 1, 1, 1, 19/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 20/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 22/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 23/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 25/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 26/27, 8/9, 2/3): 972} 
            True
        """
        n = self.order()
        if not p:
            _P = n.prime_divisors()
            if 2 in _P:
                # WHY????
                _P.remove(2)
            _P.sort( reverse = True)
        elif is_prime(p):
            return self._orbit_list(p, short = short)
        else:
            raise TypeError
        orbit_dict = dict()
        while len(_P) > 0:
            p = _P.pop()
            #print p
            orbit_dict[p] = self._orbit_list(p, short = short)
        return orbit_dict


    @cached_method
    def _orbit_list(self, p, short = False, debug = 0):
        r"""
        If this is the Jordan decomposition for $(M,Q)$, return the dictionary of
        orbits corresponding to the p-group of $M$.

        OUTPUT:
            dictionary -- the mapping orbit --> the number of elements in this orbit

        EXAMPLES:
            sage: A = FiniteQuadraticModule('3^-3.27^2')
            sage: J = JordanDecomposition(A)
            sage: J._orbit_list(3) == \
                  {(1,): 1, \
                  (3, 1, 0): 72, \
                  (3, 1, 1/3): 54, \
                  (3, 1, 2/3): 108, \
                  (3, 9, 1/3): 4, \
                  (3, 9, 2/3): 4, \
                  (9, 1, 3, 0, 1/3): 432, \
                  (9, 1, 3, 0, 2/3): 216, \
                  (9, 1, 3, 1/3, 1/3): 288, \
                  (9, 1, 3, 1/3, 2/3): 432, \
                  (9, 1, 3, 2/3, 1/3): 216, \
                  (9, 1, 3, 2/3, 2/3): 288, \
                  (9, 3, 3, 1/9, 1/3): 12, \
                  (9, 3, 3, 2/9, 2/3): 12, \
                  (9, 3, 3, 4/9, 1/3): 12, \
                  (9, 3, 3, 5/9, 2/3): 12, \
                  (9, 3, 3, 7/9, 1/3): 12, \
                  (9, 3, 3, 8/9, 2/3): 12, \
                  (27, 1, 1, 1, 1/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 2/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 4/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 5/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 7/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 8/27, 8/9, 2/3): 972, \
                  (27, 1, 1, 1, 10/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 11/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 13/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 14/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 16/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 17/27, 8/9, 2/3): 972, \
                  (27, 1, 1, 1, 19/27, 1/9, 1/3): 972, \
                  (27, 1, 1, 1, 20/27, 2/9, 2/3): 972, \
                  (27, 1, 1, 1, 22/27, 4/9, 1/3): 972, \
                  (27, 1, 1, 1, 23/27, 5/9, 2/3): 972, \
                  (27, 1, 1, 1, 25/27, 7/9, 1/3): 972, \
                  (27, 1, 1, 1, 26/27, 8/9, 2/3): 972} 
            True
        """
        if not is_prime(p):
            raise TypeError
        ppowers = copy(self._ppowers(p))
        if debug > 0: print ppowers
        if [] == ppowers:
            return dict()
        orbitdict = {(1,) : 1}

        levelpower = ppowers[len(ppowers)-1]

        def _orbit_length( r, eps, t):

            if is_even(r):
                n = Integer(r/2)
                if t.is_integral():
                    return p**(r-1) + eps * kronecker(-1,p)**n * (p**n - p**(n-1)) -1
                else:
                    return p**(r-1) - eps * kronecker(-1,p)**n * p**(n-1)
            else:
                if t.is_integral():
                    return p**(r-1)-1
                else:
                    n = Integer((r-1)/2)
                    return p**(r-1) + eps * kronecker(-1,p)**n * kronecker(2,p) * kronecker(Integer(p*t),p) * p**n

        def _multiplicitieslist():
            r"""
            Create a dictionary of possible combinations of
            reduced multiplicities
            """
            
            completemultiplicitieslist = dict()
            
            for k in range(0, valuation( levelpower, p)):

                m = p**(k+1)
                idash = len([x for x in ppowers if x < m])
                completemultiplicitieslist[k] = []
                usedrankslist = []

                for j in range(idash, len(ppowers)):
                    usedranks = [0 for x in ppowers]
                    usedranks[j] = 1
                    completemultiplicitieslist[k].append([Integer(ppowers[j]/m)])
                    usedrankslist.append(usedranks)

                for j in range(k-1,-1,-1):

                    for x in range(0,len(completemultiplicitieslist[k])):

                        multiplicities = completemultiplicitieslist[k][x]
                        usedranks = usedrankslist[x]
                        idash = len([xx for xx in ppowers if xx <= p**j])

                        completemultiplicitieslist[k][x] = [multiplicities[0]] + multiplicities

                        for jj in [xx for xx in range(idash, len(ppowers)) if usedranks[xx] < self.rank_of_jordan_component(ppowers[xx]) and ppowers[xx] < p**(j+1)*multiplicities[0]]:

                            newusedranks = usedranks[:]
                            newusedranks[jj] += 1
                            newmultiplicities = [Integer(ppowers[jj] / p**(j+1))] + multiplicities
                            completemultiplicitieslist[k].append(newmultiplicities)
                            usedrankslist.append(newusedranks)

            multiplicitieslist = []
            for k in completemultiplicitieslist.keys():
                multiplicitieslist += sorted(completemultiplicitieslist[k])
        
            return multiplicitieslist

        multiplicitieslist =  _multiplicitieslist()

        multiplicitieslist.reverse()

        tconstant = Integer(2)
        while kronecker(tconstant, p) != -1 and tconstant < p:
            tconstant += 1

        ranks = [self.rank_of_jordan_component(x) for x in ppowers]
        epsilons = [self.sign_of_jordan_component(x) for x in ppowers]
        
        while multiplicitieslist != []:

            if debug > 0: print "multiplicitieslist=", multiplicitieslist

            multiplicities = multiplicitieslist.pop()
            k = len(multiplicities)-1
            pk = p**k
            m = p*pk

            if debug > 0: print "pk={0}, m={1}, k={2}".format(pk, m, k)

            if multiplicities[0] == multiplicities[k]:

                ordersDv1 = [Integer(x / multiplicities[0]) for x in ppowers if x > multiplicities[0]]
                ranksDv1 = ranks[len(ppowers) - len(ordersDv1):]
                ordersDv1pk = [Integer(x / pk) for x in ordersDv1 if x > pk]
                ranksDv1pk = ranksDv1[len(ordersDv1)-len(ordersDv1pk):]
                if debug > 0: print "ordersDv1 = {0}, ranksDv1={1}".format(ordersDv1, ranksDv1)
                if debug > 0: print "ordersDv1pk = {0}, ranksDv1pk={1}".format(ordersDv1pk, ranksDv1pk)

                if len(ordersDv1pk) != 0 and ordersDv1pk[0] == p:

                    constantfactor = prod([min(pk, ordersDv1[j])**ranksDv1[j] for j in range(0, len(ordersDv1))]) / pk
                    if debug > 0: print "constantfactor=", constantfactor
                    constantfactor = Integer(constantfactor)
                    constantfactor *= prod(map(lambda x: p**x, ranksDv1pk[1:]))
                    rank = ranksDv1pk[0]
                    eps = epsilons[len(ranks)-len(ranksDv1pk)]
                    values = [constantfactor * _orbit_length(rank, eps, tconstant / p)]
                    values += [constantfactor * _orbit_length(rank, eps, Integer(0))]
                    values += [constantfactor * _orbit_length(rank, eps, Integer(1) / p)]

                    if short == True:

                        orbitdict[tuple([m] + multiplicities)] = tuple(values)

                    else:

                        nonzeros = [t for t in range(0,p) if values[kronecker(t,p) +1] != 0]

                        for tdash in range(0,m,p):
                            
                            for tdashdash in nonzeros:

                                tt = tdash + tdashdash
                                orbitlength = values[kronecker(tdashdash, p)+1]
                                orbit = tuple([m] + multiplicities + map(lambda x: x - floor(x), [tt * p**j / m for j in range(0, k+1)]))
                                orbitdict[orbit] = orbitlength

            else:

                maxdenominators = [p for x in multiplicities]
                for j in range(k-1,-1,-1):
                    maxdenominators[j] = Integer(max(p*multiplicities[j]/multiplicities[j+1]*maxdenominators[j+1],p))

                skips = [0] + [j+1 for j in range(0,k) if multiplicities[j+1] > multiplicities[j]]
                noskips = [j for j in range(1,k+1) if not j in skips]
                ranklist = []
                epslist = []
                constantfactor = p**(len(skips)-1-k)
                ordersD = [Integer(x / multiplicities[0]) for x in ppowers if x > multiplicities[0]]
                ranksD = ranks[len(ppowers)-len(ordersD):]

                for skip in skips[1:]:

                    quotient = Integer(multiplicities[skip] / multiplicities[skip - 1])
                    ordersA = [x for x in ordersD if x <= quotient * p**skip]
                    ranksA = ranksD[:len(ordersA)]
                    ordersB = ordersD[len(ranksA):]
                    ranksB = ranksD[len(ranksA):]
                    pj = p**(skip - 1)
                    constantfactor *= prod([min(pj, ordersA[j])**ranksA[j] for j in range(0,len(ranksA))])
                    ordersApj = [Integer(x/pj) for x in ordersA if x > pj]
                    ranksApj = ranksA[len(ranksA)-len(ordersApj):]

                    if ordersApj != [] and ordersApj[0] == p:

                        ranklist.append(ranksApj[0])
                        epslist.append(epsilons[len(epsilons)-len(ranksB)-len(ranksApj)])
                        constantfactor *= p**sum(ranksApj[1:])
                        ordersD = [Integer(x / quotient) for x in ordersB if x > quotient]
                        ranksD = ranksB[len(ranksB)-len(ordersD):]

                    else:

                        constantfactor = 0
                        break

                if constantfactor:

                    constantfactor *= prod([min(pk, ordersD[j])**ranksD[j] for j in range(0,len(ordersD))])
                    ordersDpk = [Integer(x / pk) for x in ordersD if x > pk]
                    ranksDpk = ranksD[len(ranksD)-len(ordersDpk):]

                    if ordersDpk != [] and ordersDpk[0] == p:

                        ranklist.append(ranksDpk[0])
                        epslist.append(epsilons[len(epsilons)-len(ranksDpk)])
                        constantfactor *= p**sum(ranksDpk[1:])

                    else:

                        constantfactor = 0

                if constantfactor:

                    product = [constantfactor] + [0 for j in skips[2:]]
                    skipindex = 0
                    tpjvalues = [0 for j in skips]
                    tpjs = [[x / maxdenominators[0] for x in range(0,maxdenominators[0])]] + [[] for j in skips[1:]]

                    # if debug > 0: print "tpjs", tpjs
                    
                    while tpjs[0] != []:

                        if tpjs[skipindex] == []:

                            skipindex -= 1
                            tpjs[skipindex].remove(tpjvalues[skipindex])

                        else:

                            if skipindex == len(skips)-1:

                                for tpj in tpjs[skipindex]:

                                    tpjvalues[skipindex] = tpj
                                    tpk = p**(k - skips[skipindex]) * tpj
                                    factor = product[len(product) - 1]
                                    t = p**(skips[skipindex] - skips[skipindex - 1] - 1) * tpjvalues[skipindex - 1]
                                    t -= multiplicities[skips[skipindex]] / multiplicities[skips[skipindex] - 1] / p * tpj
                                    orbitlength1 = _orbit_length(ranklist[skipindex - 1], epslist[skipindex - 1], t)
                                    orbitlength2 = _orbit_length(ranklist[skipindex], epslist[skipindex], tpk)
                                    orbitlengths = orbitlength1 * orbitlength2

                                    if orbitlengths != 0:

                                        reducednorms = [0 for j in range(0,k+1)]
                                        for j in range(0,len(skips)):
                                            reducednorms[skips[j]] = tpjvalues[j]
                                        for j in noskips:
                                            t = p*reducednorms[j-1]
                                            reducednorms[j] = t - floor(t)

                                        orbitdict[tuple([m] + multiplicities + reducednorms)] = factor * orbitlengths

                                skipindex -= 1
                                tpjs[skipindex].remove(tpjvalues[skipindex])

                            else:

                                tpjvalues[skipindex] = tpjs[skipindex][0]

                                if skipindex > 0:
                                    
                                    t = p**(skips[skipindex] - skips[skipindex - 1] - 1) * tpjvalues[skipindex - 1]
                                    t -= multiplicities[skips[skipindex]] / multiplicities[skips[skipindex] - 1] / p * tpjvalues[skipindex]
                                    
                                    orbitlength = _orbit_length(ranklist[skipindex - 1], epslist[skipindex - 1], t)

                                    if orbitlength == 0:

                                        tpjs[skipindex].remove(tpjvalues[skipindex])

                                    else:
                                        maxdenominator = maxdenominators[skips[skipindex + 1]]
                                        tcandidates = [t/maxdenominator for t in range(0,maxdenominator)]
                                        difference = skips[skipindex + 1] - skips[skipindex]
                                        quotient = multiplicities[skips[skipindex + 1]] / multiplicities[skips[skipindex]]
                                        tpjs[skipindex + 1] = [t for t in tcandidates if (quotient * t - p**difference * tpjvalues[skipindex]).is_integral()]
                                        product[skipindex] = orbitlength * product[skipindex - 1]
                                        skipindex += 1

                                else:

                                    maxdenominator = maxdenominators[skips[skipindex + 1]]
                                    tcandidates = [t/maxdenominator for t in range(0,maxdenominator)]
                                    difference = skips[skipindex + 1] - skips[skipindex]
                                    quotient = multiplicities[skips[skipindex + 1]] / multiplicities[skips[skipindex]]
                                    tpjs[skipindex + 1] = [t for t in tcandidates if (quotient * t - p**difference * tpjvalues[skipindex]).is_integral()]

                                    skipindex += 1
                                    
        return orbitdict

    def values( self, debug = 0):
        r"""
        If this is the Jordan decomposition for $(M,Q)$, return the values of $Q(x)$ ($x \in M$) as a dictionary d.

        OUTPUT:
            dictionary -- the mapping Q(x) --> the number of elements x with the same value Q(x)

        EXAMPLES:
            sage: A = FiniteQuadraticModule('3^-3.27^2')
            sage: J = JordanDecomposition(A)
            sage: J.values() == \
                  {0: 729, \
                  1/27: 972, \
                  2/27: 972, \
                  4/27: 972, \
                  5/27: 972, \
                  7/27: 972, \
                  8/27: 972, \
                  1/3: 810, \
                  10/27: 972, \
                  11/27: 972, \
                  13/27: 972, \
                  14/27: 972, \
                  16/27: 972, \
                  17/27: 972, \
                  2/3: 648, \
                  19/27: 972, \
                  20/27: 972, \
                  22/27: 972, \
                  23/27: 972, \
                  25/27: 972, \
                  26/27: 972}
            True
            sage: A = FiniteQuadraticModule('2_3^-3.4^2.8_2^-2')
            sage: J = JordanDecomposition(A)
            sage: J.values() == \
                  {0: 480, \
                  1/8: 512, \
                  3/16: 1024, \
                  1/4: 480, \
                  3/8: 512, \
                  7/16: 1024, \
                  1/2: 544, \
                  5/8: 512, \
                  11/16: 1024, \
                  3/4: 544, \
                  7/8: 512, \
                  15/16: 1024}
            True
        """
        n = self.order()

        values = [1]
        
        def combine_lists( list1, list2):
            N1 = len(list1)
            N2 = len(list2)
            newlength = lcm(N1,N2)
            newlist = [0 for j1 in range(0,newlength)]
            for j1 in range(0,N1):
                n1 = list1[j1]
                if n1 != 0:
                    for j2 in range(0,N2):
                        n2 = list2[j2]
                        if n2 != 0:
                            newlist[(j1 * Integer(newlength / N1) + j2 * Integer(newlength / N2)) % newlength] += (n1 * n2)
            return newlist        

        def values_even2adic(gs):
            l, n, eps, t, o = gs._symbol_dict[2][0]
            n /= 2
            factor = 2**((l-1)*n)
            if n == 1 and eps == 1:
                return [factor * (l+2)] + [factor * (valuation(j,2)+1) for j in range(1,2**l)]
            else:
                quotient = Integer(2**n-eps)/Integer(2**(n-1)-eps)
                return [factor * (quotient * (2**((n-1)*(l+1))-eps**(l+1)) + eps**(l+1))] + [factor * quotient * (2**((n-1)*(l+1)) - eps**(valuation(j,2)+1) * 2**((n-1)*(l-valuation(j,2)))) for j in range(1,2**l)] 
            
        def values_odd2adic(gs):
            p = 2
            l, n, eps, tp, t = gs._symbol_dict[2][0]
            # t = t%8
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
            else:
                raise TypeError

            level = 2**(l+1)
            squarerepresentationlist = [0 for j in range(0,level)]
            if is_even(l+1):
                squarerepresentationlist[0] = squarerepresentationlist[2**(l-1)] = 2**((l+1)/2)
            else:
                squarerepresentationlist[0] = squarerepresentationlist[2**l] = 2**(l/2)
            for k in range(0,l-1,2):
                if debug > 0: print "k:", k
                for a in range(1, 2**(l+1-k),8):
                    if debug > 0: print "a:", a
                    squarerepresentationlist[2**k * a] = 2**(k/2 + 2)
            if debug > 0: print "Test the squarelist:", sum(squarerepresentationlist) == level, squarerepresentationlist, level

            if debug > 0: print "tvalues", tvalues
            
            t1inverse = inverse_mod(tvalues[0], level)
            values = [squarerepresentationlist[(j * t1inverse)%level]/2 for j in range(0,level)]

            if len(tvalues) > 1: #The following works only for tvalues where the last elements coincide

                t2inverse = inverse_mod(tvalues[1], level)
                newvalues = [squarerepresentationlist[(j * t2inverse)%level]/2 for j in range(0,level)]

                for j in range(1,len(tvalues)):
                    values = combine_lists(values, newvalues)

            neven = n - len(tvalues)
            if neven > 0:
                values = combine_lists(values, values_even2adic(GenusSymbol('' + str(2**l) + '^+' + str(neven))))
            
            return values

                
        _P = n.prime_divisors()
        if 2 in _P:

            _P.remove(2)
            
            l = copy(self._ppowers(2))
            while l != []:
                q = l.pop()
                gs = self.jordan_component(q)
                if gs.is_odd():
                    values = combine_lists(values, values_odd2adic(gs))
                else:
                    values = combine_lists(values, values_even2adic(gs))
                if debug > 0: print values

        _P.sort( reverse = True)

        while [] != _P:

            p = _P.pop()
            if debug > 0: print "p = ", p
            shortorbitdict = self.orbit_list(p, short = True)
            level = max(self._ppowers(p))
            newvalues = [0 for j in range(0,level)]
            newvalues[0] = 1
            
            for orbit in shortorbitdict.keys():

                if orbit != (1,):
                    
                    k = Integer(valuation(orbit[0],p)-1)
                    # if debug > 0: print orbit
                    v1 = orbit[1]
                    if v1 == orbit[k+1]:
                    
                        orbitlengthsbykronecker = shortorbitdict[orbit]
                        for t1 in range(0,p**(k+1)):
                            newvalues[Integer(v1 * t1 * level / p**(k+1)) % level] += orbitlengthsbykronecker[kronecker(t1,p) + 1]

                    else:

                        newvalues[Integer(v1 * orbit[k+2] * level) % level] += shortorbitdict[orbit]

                    # if debug > 0: print "Position1:", sum(newvalues)
            # if debug > 0: print "1:", values
            # if debug > 0: print "2:", newvalues
            values = combine_lists(values, newvalues)
            # if debug > 0: print "3:", values
            # if debug > 0: print "Position2:", values, _P, p

        # if debug > 0: print "Position3:", values
            
        valuesdict = {Integer(j)/len(values) : values[j] for j in range(0,len(values)) if values[j] != 0}

        # if debug > 0: print "Position4:", values, valuesdict, "END"
            
        return valuesdict #, values

    def two_torsion_values( self):
        r"""
        If this is the Jordan decomposition for $(M,Q)$, return the values of $Q(x)$
        for $x \in M_2=\{x \in M | 2*x = 0\}$, the subgroup of two-torsion elements as a dictionary.

        OUTPUT:
            dictionary -- the mapping Q(x) --> the number two-torsion elements x with the same value Q(x)

        EXAMPLES:
            sage: A = FiniteQuadraticModule('2_3^-3.4^2.8_2^-2')
            sage: J = JordanDecomposition(A)
            sage: J.two_torsion_values() == {0: 48, 1/4: 16, 1/2: 16, 3/4: 48}
            True
        """
        n = self.order()

        values = [1]
        
        def combine_lists( list1, list2):
            N1 = len(list1)
            N2 = len(list2)
            newlength = lcm(N1,N2)
            newlist = [0 for j1 in range(0,newlength)]
            for j1 in range(0,N1):
                n1 = list1[j1]
                if n1 != 0:
                    for j2 in range(0,N2):
                        n2 = list2[j2]
                        if n2 != 0:
                            newlist[(j1 * Integer(newlength / N1) + j2 * Integer(newlength / N2)) % newlength] += (n1 * n2)
            return newlist        

        def two_torsion_values_even2adic(gs):
            l, n, eps, t, o = gs._symbol_dict[2][0]
            n /= 2
            fourn = 4**n
            if l == 1:
                epstwon = eps * 2**n
                return [(fourn + epstwon)/2, (fourn - epstwon)/2]
            else:
                return [fourn]
                
        def two_torsion_values_odd2adic(gs):
            l, n, eps, tp, t = gs._symbol_dict[2][0]
            if l == 1:
                # if debug > 0: print "n:", n, "eps:", eps, "t:", t, "n-t:", n-t, (n-t)/2
                if eps == -1:
                    t = (t + 4) % 8
                n2 = ((n - t)/2) % 4
                n1 = n - n2
                # if debug > 0: print "n1:", n1, "n2:", n2, "t:", t
                list1 = [sum([binomial(n1,k) for k in range(j,n1+1,4)]) for j in range(0,4)]
                # if debug > 0: print list1
                if n2 == 0:
                    return list1
                else:
                    list2 = [[1,0,0,1],[1,0,1,2],[1,1,3,3]][n2 - 1]
                    # if debug > 0: print list2
                    return combine_lists(list1, list2)
            elif l == 2:
                twonminusone = 2**(n-1)
                return [twonminusone, twonminusone]
            else:
                return [2**n]
            
        for gs in self.jordan_components(2):
            if gs.order()==1:
                continue
            if gs.is_odd():
                values = combine_lists(values, two_torsion_values_odd2adic(gs))
            else:
                values = combine_lists(values, two_torsion_values_even2adic(gs))
            
        valuesdict = {Integer(j)/len(values) : values[j] for j in range(0,len(values)) if values[j] != 0}

        return valuesdict #, values

    def torsion(self, m):
        fac = self._torsion_factors(m)
        if fac == None:
            return 1
        else:
            return prod([p ** r for p, r in fac])

    def _torsion_factors(self, m):
        if not is_prime_power(m):
            raise NotImplementedError
        p, r = Integer(m).factor()[0]
        J = self.jordan_components(p)
        if J == [GenusSymbol('1^+1')]:
            return None
        nt = list()
        for s in J:
            n = s.valuation(p)
            nt.append([p, s.p_rank(p) * min(n, r)])
        return nt

    def sigma(self, s):
        res = Integer(1)
        for p in self.level().prime_factors():
            res = res * (Integer(1) + sum([p ** (r * s + self._torsion_factors(p ** r)[0][1] / Integer(2))
                                  for r in range(1, self.level().valuation(p) + Integer(1))]))
        return res

    def oddity(self):
        if not self._symbol_dict.has_key(2):
            return 0
        else:
            return (sum([_[4] for _ in self._symbol_dict[2]]) + 4 * len([_ for _ in self._symbol_dict[2] if is_odd(_[0]) and _[2] == -1])) % 8

    @cached_method
    def dimension_estimate_for_anisotropic(self, k, use_simple_est=False):
        N = self.level()
        A2 = self.torsion(2)
        A3 = self.torsion(3)
        A = self.order()
        d = RR(A + A2) / 2
        sqA2 = RR(sqrt(A2))
        sqA3 = RR(sqrt(A3))
        sqA = RR(sqrt(A))
        s = self.sigma(-1)
        #a5est = sqA/(2*pi)*(3/2+ln(N))*(s-sqA/N)
        # print "d = %d, A2 = %d, A3 = %d, s = %d, a5est = %d"%(d,A2,A3,s,
        # a5est)
        return d * RR(k - 1) / RR(12) - sqA2 / 4 - RR(1 + sqA3) / RR(3 * sqrt(3)) - A2 / RR(8) - RR(1) / RR(2) \
               - self.beta_est(use_simple_est) / RR(2)

    def beta(self):
        x = [BB(a) * m for a, m in self.values().iteritems()]
        return sum(x)

    def gaussum(self, s, p=None, F=CC):
        o = self.order() if p == None else p ** self.order().valuation(p)
        return F(self.char_invariant(s, p)[0] * self.char_invariant(s, p)[1] * o)

    def eps(self, p=None):
        a = self.gaussum(1, p)
        return a / abs(a)

    def chi(self, n, p=None):
        return self.gaussum(n, p) / self.gaussum(1, p)

    def beta_formula(self, debug=0):
        prec = max(log(self.order(), 2), 53)
        RF = RealField(prec)
        A = self.order()
        q = 1
        N = Integer(self.level())
        if debug > 0:
            print "N={0}".format(N)
        for p in N.prime_factors():
            c = self.jordan_components(p)[0]._symbol_dict[p][0]
            if len(c) == 3:
                if c[1] == 2:
                    q = q * p
            elif c[3] == 0 and c[1] == 2:
                q = q * 2
        if debug > 2:
            print A, N, q
        r1 = lambda d: (-1) ** (len(Integer(gcd(d, q)).prime_factors()))

        R2 = self.p_rank(2)
        if debug > 0:
            print "R2 = {0}".format(R2)

        def r2(d):
            if R2 == 0:
                return 1
            elif is_odd(d):
                return 2 ** (R2 - 2)
            else:
                return 2 ** (floor(R2 / 2) - 1)

        def r3(d):
            R3 = Integer(
                len([_ for _ in Integer(d / gcd(d, q)).prime_factors() if _ % 4 == 3]))
            if is_odd(R3):
                return kronecker(-4, R3)
            else:
                return (-1) ** (R3 / 2)

        def eps_odd(d):
            dd = odd_part(d / gcd(d, q))
            a = kronecker(N / d, odd_part(dd))
            sig = lambda p: self.jordan_component(p)._symbol_dict[p][0][2]
            a *= prod(sig(p) * kronecker(8, p) for p in dd.prime_factors())
            return a

        delta = kronecker(-4, R2)

        def eps2(d):
            d = Integer(d)
            if N.valuation(2) == 1:
                dd = d / (gcd(d, q))
                if d % 4 == 2:
                    if dd % 4 == 3:
                        return 1
                    else:
                        return 0
                elif d % 4 == 0:
                    return 2

            if is_odd(d) or d % 4 == 2:
                return 1

            N2 = self.level() / odd_part(self.level())
            dd = d / ((gcd(N2, d)) * gcd(d, q))
            t = (self.oddity() / R2) % 8
            s = len(self.jordan_components(2))
            if s == 2:
                if debug > 0:
                    print "s = 2"
                t1 = self.jordan_component(2)._symbol_dict[2][0][4]
                t2 = self.jordan_component(4)._symbol_dict[2][0][4]
                t = t2 / t1 % 8
                if debug > 1:
                    print "t = {0}".format(t)
                if d.valuation(2) == 1 or d.valuation(2) == 2:
                    return 0
                dd = d / (8 * gcd(d, q))
                if debug > 1:
                    print "d = {0}, dd =  {1}".format(d, dd)
                if dd % 4 == 3:
                    if (t + 1) % 8 in [2, 6]:  # d.valuation(2) == 0:
                        return 0
                    a = kronecker(8, N / d) * kronecker(2, t)
                else:
                    if (t + 1) % 4 == 0 and dd.valuation(2) == 0:
                        if debug > 1:
                            print "returning 0 for t = {0} and d = {1}".format(t, d)
                        return 0
                    a = kronecker(-8, N / d) * kronecker(2, t)
                    if debug > 1:
                        print "a = {0}".format(a)
            else:
                if dd % 4 == 3:
                    a = delta * \
                        kronecker(
                            N2 / gcd(N2, N / d), (N / d) / gcd(N2, N / d) * t)
                else:
                    a = kronecker(-N2 / gcd(N2, N / d),
                                  (N / d) / gcd(N2, N / d) * t)
            if debug > 1:
                print "d = {0}, eps2(d) = {1}, delta = {2}".format(d, a, delta)
            return a

        eps = lambda d: eps2(d) * eps_odd(d) * r1(d) * r2(d) * r3(d)

        if debug > 0:
            for d in N.divisors():
                if d * gcd(d, q) % 4 in [0, 3]:
                    print "d = {0}, r1(d) = {1}, r2(d) = {2}, r3(d) = {3}, eps_odd(d) = {4}, eps2(d) = {5}, H(-d(q,d)) = {6}".format(d, r1(d), r2(d), r3(d), eps_odd(d), eps2(d), h(d*gcd(d,q), prec))
        return -sum(q / gcd(d, q) * eps(d) * h(d * gcd(d, q), prec) for d in N.divisors() if d * gcd(d, q) % 4 in [0, 3])

    def beta_est(self, simple_est=False, debug=0):
        prec = max(log(self.order(), 2), 53)
        RF = RealField(prec)
        A = self.order()
        q = Integer(1)
        N = self.level()
        if debug > 0:
            print "N={0}".format(N)
        for p in N.prime_factors():
            c = self._symbol_dict[p]
            if len(c) == 1:
                if len(c[0]) == 3:
                    if c[0][1] == 2:
                        q = q * p
                elif c[0][3] == 0 and c[0][1] == 2:
                    q = q * 2

        R2 = self.p_rank(2)
        if debug > 0:
            print "R2 = {0}".format(R2)

        def r2(d):
            if R2 == 0:
                return 1
            elif is_odd(d):
                return 2 ** (R2 - 2)
            else:
                return 2 ** (floor(R2 / 2) - 1)
        if simple_est:
            if debug > 0:
                print "simple estimate for {}".format(self)
            hh = lambda d: log(d) * sqrt(d) / RF.pi()
        else:
            hh = h
        return sum(q / gcd(d, q) * r2(d) * hh(d * gcd(d, q)) for d in N.divisors() if d * gcd(d, q) % 4 in [0, 3])

    #@cached_method
    def sigmag(self):
        N = self.level()
        res = 1
        for p in self.level().prime_factors():
            resp = 0
            for c in self.jordan_components(p):
                for r in range(0, c.level().valuation(p) + 1):
                    g = c.char_invariant(p ** r)
                    # print g
                    resp = resp + abs(imag_part(CC(g[0])) / RR(p ** r))
            res = res * resp
        return res * RR(sqrt(self.order()))

    def _component_values(self, p):
        vals = []
        J = self.jordan_components(p)
        for c in J:
            if p == 2:
                M = c.finite_quadratic_module()
                vals.append(M.values())
                continue
            n = c.valuation(p)
            q = p ** n
            if c.jordan_component(q)._symbol_dict[p][0][2] * kronecker(2, p) ** c.p_rank(p) == -1:
                if p % 4 == 3:
                    a = -1
                else:
                    a = primitive_root(p)
            else:
                a = 1
            # print k
            #vc[0] = p**k
            # print vc
            #vc[Integer(a % p**n)/p**n] = 1
            vc = self._rank_one_values(p, n, a)
            r = c.p_rank(p)
            # print r
            if r > 1:
                # print p, n, c.jordan_component(q)[0][2]
                if p != 2 and is_even(r) and c.jordan_component(q)._symbol_dict[p][0][2] != 1:
                    vc2 = self._rank_one_values(p, n, 1)
                    r -= 1
                else:
                    vc2 = None
                values_comb = itertools.combinations_with_replacement(vc, r)
                vc = self._combine_values(vc, values_comb, r, q)
                # print vc, vc2
                if vc2 != None:
                    vcnew = {}
                    for v1 in vc:
                        for v2 in vc2:
                            # print v1,v2
                            val = Integer((v1 + v2) * q % q) / q
                            mult = vc[v1] * vc2[v2]
                            if not vcnew.has_key(val):
                                vcnew[val] = mult
                            else:
                                vcnew[val] += mult
                    vc = vcnew
            vals.append(vc)
        return vals

    def _combine_values(self, vc, values_comb, r, q):
        vcnew = {}
        for v in values_comb:
            val = Integer(sum(vv * q for vv in v) % q) / q
            mult = prod(vc[vv] for vv in v)
            R = r
            for vv in uniq(v):
                a = v.count(vv)
                mult *= binomial(R, a)
                R -= a
            # print val, mult
            if not vcnew.has_key(val):
                vcnew[val] = mult
            else:
                vcnew[val] += mult
        return vcnew

    @cached_method
    def values_stupid(self):
        ps = self.level().prime_factors()
        levels = []
        for p in ps:
            for c in self.jordan_components(p):
                levels.append(c.level())
        vc = flatten([self._component_values(p) for p in ps], max_level=1)
        # print "vc = ", vc
        only_vals = map(lambda x: x.keys(), vc)
        vals = itertools.product(*only_vals)
        # print list(vals)
        vccomb = {}
        N = self.level()
        # print vals
        for v in vals:
            val = sum(v[i] for i in range(len(levels)))
            val = (val * N % N) / N
            mult = prod(vc[i][v[i]] for i in range(len(v)))
            if not vccomb.has_key(val):
                vccomb[val] = mult
            else:
                vccomb[val] += mult
        return vccomb

    def _rank_one_values(self, p, n, a):
        # print "a=", a
        q = p ** n
        vc = {}
        if is_even(n):
            k = Integer(n) / 2
            kk = k
        else:
            k = Integer(n - 1) / 2
            kk = k + 1
        if p != 2:
            Q1 = [(x * x) % p for x in range(1, p / 2 + 1)]
            Q = [Integer(x) for x in xrange(q) if x % p in Q1]
        else:
            Q1 = [1, 7]
            Q = [Integer(x) for x in xrange(q) if x % 8 in Q1]
        Q = Q + uniq([(m * p ** (2 * r)) % q for r in range(1, kk) for m in Q])
        Q.append(0)
        # print "Q=", Q
        # print Q1, Q
        for x in Q:
            nom = Integer((x * a) % q)
            val = Integer((x * a) % q) / q
            if not p.divides(nom):
                mult = 2
            else:
                if nom == 0:
                    mult = p ** k
                else:
                    r = nom.valuation(p)
                    mult = 2 * p ** (r / 2)
            # print val
            if not vc.has_key(val):
                vc[val] = mult
            else:
                vc[val] += mult
        return vc

    def char_invariant(self, s, p=None, debug=0):
        r"""
        If this quadratic module equals $A = (M,Q)$, return
        the characteristic function of $A$ (or $A(p)$ if $p$ is a prime)
        at $s$, i.e. return
        $$\chi_A (s)= |M|^{-1}\sum_{x\in M} \exp(2\pi i s Q(x))).$$

        NOTE
            We apply the formula in [Sko, Second Proof of Theorem 1.4.1].
            Code taken from FQM package

        EXAMPLES NONE
        """
        # manual caching
        s = s % self.level()
        if self.__sigma.has_key((s, p)):
            return self.__sigma[(s, p)]

        #t = cputime()
        if s == 0:
            return 1, 1
        if not p is None and not is_prime(p):
            raise TypeError
        if p and 0 != self.order() % p:
            return 1, 1
        _p = p

        K = self._K
        z = self._z

        jd = self.jordan_decomposition(flat = True)

        ci = ci1 = 1
        for p, c in jd:
            # c: basis, ( prime p,  valuation of p-power n, dimension r,
            # determinant d over p [, oddity o])
            n = c.valuation(p)
            r = c.p_rank(p)
            d = c._eps(p, n)
            if debug > 0: print "p={0}, n={1}, r={2}, d={3}".format(p,n,r,d)
            if _p and p != _p:
                continue
            o = None if p != 2 else (0 if c.is_even() else c._symbol_dict[2][0][4])
            if debug > 0: print "o=",o
            odd = c.is_odd()
            k = valuation(s, p)
            s1 = Integer(s / p ** k)
            h = max(n - k, 0)
            if debug > 0: print "h={0}".format(h)
            q = p ** h
            if p != 2:
                lci = z ** ((r * (1 - q)) % 8) * d ** (h % 2) if h > 0 else 1
                lci1 = q ** (-r) if h > 0 else 1
            elif k == n and odd:
                # print "t!"
                return 0, 0
            else:
                f = z ** o if odd else 1
                lci = f * d ** (h % 2) if h > 0 else 1
                lci1 = q ** (-r) if h > 0 else 1
                if debug > 0: print "f={0}, d={1}, lci={2}".format(f, d, lci)
            if 2 == p:
                lci = lci ** s1
            if debug > 0: print "lci=",lci
            if debug > 0: print "lci1=", lci1
            ci *= lci * kronecker(s1, 1 / lci1)
            ci1 *= lci1
        v = (ci, QQ(ci1).sqrt())
        self.__sigma[(s, p)] = v
        return v

    @cached_method
    def two_torsion_values_stupid(self):
        J = self.jordan_components(2)
        vals = dict()
        for s in J:
            svals = {}
            if s.valuation(2) >= 3 or (s.is_even() and s.valuation(2) >= 2):
                svals = {0: 2 ** s.p_rank(2)}
            else:
                if s.is_even():
                    if s.valuation(2) == 1:
                        n = s.p_rank(2) / 2
                        ll = [3 ** (n - 2 * k) * binomial(n, 2 * k)
                              for k in range(0, n / 2 + 1)]
                        oh = sum(ll)
                        if s.oddity() == 4:
                            svals = {
                                0: 2 ** s.p_rank(2) - oh, QQ(1) / QQ(2): oh}
                        else:
                            svals = {
                                0: oh, QQ(1) / QQ(2): 2 ** s.p_rank(2) - oh}
                else:
                    # TODO: improve this part as well
                    M = s.finite_quadratic_module()
                    svals = M.kernel_subgroup(2).as_ambient()[0].values()

            if vals == {}:
                vals = svals
            else:
                vals_new = dict()
                for k, m in svals.iteritems():
                    for kk, mm in vals.iteritems():
                        den = lcm(QQ(k).denominator(), QQ(kk).denominator())
                        v = (((k + kk) * den) % den) / Integer(den)
                        if not vals_new.has_key(v):
                            vals_new[v] = m * mm
                        else:
                            vals_new[v] += m * mm
                vals = vals_new
        return vals

    def valuation(self, p):
        r'''Return the p-valuation of the level of self
        '''
        if not self._symbol_dict.has_key(p):
            return 0
        if not isinstance(self._symbol_dict[p], list):
            return 0
        if len(self._symbol_dict[p]) == 0:
            return 0
        return max(_[0] for _ in self._symbol_dict[p])

    @cached_method
    def level(self):
        l = Integer(prod([p ** self.valuation(p)
                          for p in self._symbol_dict.keys()]))
        # print l
        if self.p_rank(2) > 0:
            ll = [_[0] for _ in self._symbol_dict[2] if _[3] == 1]
            if ll == []:
                return l
            if max(ll) == self.valuation(2):
                l = l * 2
        return l

    @cached_method
    def signature(self):
        sig = 0
        if len(self._symbol_dict) == 0:
            return 0
        for p, l in self._symbol_dict.iteritems():
            if p == 2:
                for s in l:
                    sig = sig + s[4] + \
                        (4 if is_odd(s[0]) and s[2] == -1 else 0)
                    sig = sig % 8
            else:
                for s in l:
                    eps = s[2]
                    n = s[1]
                    r = s[0]  # symbol= q^eps*n, where q = p^r
                    # print r,n,eps
                    if r % 2 == 0:
                        continue
                    sig += n * (1 - p ** r) % 8 + \
                        (4 * r if eps == -1 else 0) % 8
        return Integer(sig % 8)

    @cached_method
    def is_simple(self, k, no_inv=False, aniso_formula=False, reduction=True, bound=0):
        d = self.dimension_cusp_forms(
            k, no_inv, aniso_formula, test_positive=True if bound == 0 else False, reduction=reduction)
        if d < 0:
            raise ValueError("Negative dimension for {0}".format(self))
        if d <= bound:
            return True
        else:
            return False

    def is_global(self, r, s, even=True):
        r""" Checks if this symbol can be realized as
             the genus symbol of an (even if flag is set) integral lattice
             of type (r,s).
        """
        if not even:
            raise NotImplementedError("Odd lattices are not supported so far")
        D = self.order() * (-1) ** s
        # print D
        if even and (r - s) % 8 != self.signature():
            return False
        for p in self.level().prime_factors():
            if self.p_rank(p) > r + s:
                return False
            elif self.p_rank(p) == r + s:
                eps = self._eps(p,total=True)
                a = D / p ** (self.order().valuation(p))
                if p == 2:
                    A2 = self.jordan_component(2)
                    if A2.is_odd():
                        continue
                if not eps == kronecker(a, p):
                    return False
        return True

    def is_global_unique(self, r, s):
        r"""
          Returns True if there is only one lattice in the genus of a
          global realization of self. We apply Theorem 1.13.2 of [Ni].
          This is a sufficient but not a necessary condition.
          Therefore, we return None if the condition is not satisfied.
        """
        if not self.is_global(r,s):
            raise RuntimeError("The finite quadratic module is not global!")
        r = Integer(r)
        s = Integer(s)

        nonstr = "The criterion is not satisfied. We cannot decide if the finite quadratic module is unique."

        if not (r >= 1 and s >= 1 and r+s >= 3):
            print nonstr
            return None
        
        for p in self.level().prime_factors():
            satisfied = True
            if not (r+s >= 2 + self.p_rank(p)):
                satisfied = False
            if p > 2 and not satisfied:
                found = False
                for j in self.jordan_components(p):
                    if j.p_rank(p) >= 2:
                        found = True
                        break
                if not found:
                    print nonstr
                    return None
            if p == 2 and not satisfied:
                found = False
                for j in self.jordan_components(2):
                    if j.is_odd():
                        jj = self.jordan_component(2**(j.valuation(2)+1))
                        if jj.p_rank(p) > 0 and jj.is_odd():
                            found = True
                            break
                    if j.p_rank(2) >= 2:
                        try:
                            j - U(2**(j.valuation(2)))
                            found = True
                            break
                        except ValueError:
                            try:
                                j - V(2**(j.valuation(2)))
                                found = True
                                break
                            except ValueError:
                                continue
                if not found:
                    print nonstr
                    return None
        return True

    def _eps(self, q, n=None, total=False):
        if not Integer(q).is_prime_power():
            raise ValueError("q={0} has to be a prime power".format(q)) 
        p = q.prime_factors()[0]
        if n is None and not total:
            # if n is given, we assume that p is a prime and n is the valuation
            n = q.valuation(p)
        if not self._symbol_dict.has_key(p):
            return 1
        l = self._symbol_dict[p]
        if len(l) == 0:
            return 1
        if total:
            return Integer(prod(s[2] for s in l))
        else:
            return Integer(prod(s[2] for s in l if s[0] == n))

    @cached_method
    def dimension_modular_forms(self, k, no_inv=False, aniso_formula=False, test_positive=False, reduction=False):
        r"""
          Computes the dimension of the space of modular forms of weight $k$
          for the Weil representation associated with this finite quadratic module.

          INPUT:
          - k: a half-integer, the weight, >= 2
          - no_inv: bool, if True: we do not compute invariants in the case of weight 2 (so assume they are 0)
          - aniso_formula: bool, if True use the formula involving class numbers to compute the dimension.
                           works only for anisotropic modules. The formula is given in Theorem XX of [BEF].
          - test_positive: bool, if True, only test if the dimension is positive
                           returns a positive number if this is the case,
                           which is not necessarily equal to the dimension.
          - reduction: bool, if True, we use reduction mod p to compute the invariants
                             of the Weil representation, whose dimension is needed for $k = 3/2$ and $k=2$.

          OUTPUT:
          - an Integer, the dimension of the space of cusp forms of weight $k$
          for the Weil representation associated with this finite quadratic module

          SEE ALSO:
          - For more details, see the implementation in PSAGE.
        """
        s = str(self)
        if not s == '1^+1':
            #M = FiniteQuadraticModule(s)
            V = VectorValuedModularForms(
                s, True, aniso_formula=aniso_formula, use_reduction=reduction)
            d = V.dimension(
                k, no_inv=no_inv, test_positive=test_positive)
        else:
            d = dimension_modular_forms(1, k)
        return d

    @cached_method
    def dimension_cusp_forms(self, k, no_inv=False, aniso_formula=False, test_positive=False, reduction=False):
        r"""
          Computes the dimension of the space of cusp forms of weight $k$
          for the Weil representation associated with this finite quadratic module.

          INPUT:
          - k: a half-integer, the weight, >= 3/2
          - no_inv: bool, if True: we do not compute invariants in the case of weight 2 (so assume they are 0)
          - aniso_formula: bool, if True use the formula involving class numbers to compute the dimension.
                           works only for anisotropic modules. The formula is given in Theorem XX of [BEF].
          - test_positive: bool, if True, only test if the dimension is positive
                           returns a positive number if this is the case,
                           which is not necessarily equal to the dimension.
          - reduction: bool, if True, we use reduction mod p to compute the invariants
                             of the Weil representation, whose dimension is needed for $k = 3/2$ and $k=2$.

          OUTPUT:
          - an Integer, the dimension of the space of cusp forms of weight $k$
          for the Weil representation associated with this finite quadratic module

          SEE ALSO:
          - For more details, see the implementation in PSAGE.
        """
        s = str(self)
        if not s == '1^+1':
            #M = FiniteQuadraticModule(s)
            V = VectorValuedModularForms(
                s, True, aniso_formula=aniso_formula, use_reduction=reduction)
            d = V.dimension_cusp_forms(
                k, no_inv=no_inv, test_positive=test_positive)
        else:
            d = dimension_cusp_forms(1, k)
        return d

    def is_even(self):
        r'''
         Returns True if there is no odd 2-adic Jordan component.
        '''
        if self.p_rank(2) == 0:
            return True
        else:
            for s in self._symbol_dict[2]:
                if s[3] == 1:
                    return False
        return True

    def is_odd(self):
        return not self.is_even()

    def jordan_components(self, p):
        r'''
        Returns all p-adic Jordan components of self as a list GenusSymbols.
        '''
        if not self._symbol_dict.has_key(p):
            return [GenusSymbol()]
        self._reduce()
        return [GenusSymbol({p: [x]}) for x in self._symbol_dict[p]]

    def jordan_decomposition(self, flat = False):
        l = {}
        for p in self.level().prime_factors():
            l[p] = [c for c in self.jordan_components(p)]
        if not flat:
            return l
        else:
            l1 = []
            for p in l.keys():
                l1 += [(p,c) for c in l[p]]
            return l1

    def jordan_component(self, q):
        if not is_prime_power(q):
            raise ValueError
        else:
            p, n = list(Integer(q).factor())[0]

        if not self._symbol_dict.has_key(p):
            return GenusSymbol('1^+1')
        else:
            r = []
            for s in self._symbol_dict[p]:
                if s[0] == n:
                    r.append(s)
            if len(r) == 0:
                return GenusSymbol('1^+1')
            else:
                return GenusSymbol({p: r})

    def rank_of_jordan_component(self, q):
        if not is_prime_power(q):
            raise ValueError("q (={0}) has to be a prime power".format(q))
        c = self.jordan_component(q)
        if c.order() == 1:
            return 0
        return c.p_rank(q.prime_factors()[0])

    def sign_of_jordan_component(self,q):
        if not is_prime_power(q):
            raise ValueError("q (={0}) has to be a prime power".format(q))
        c = self.jordan_component(q)
        if c.order() == 1:
            return 1
        return c._symbol_dict[q.prime_factors()[0]][0][2]

    def max_rank(self):
        r = 0
        for p in self.level().prime_factors():
            r = max(r, self.p_rank(p))
        return r

    def B(self, m):
        r'''
        Computes the B-Set of this symbol by brute force.
        '''
        from sfqm.Bsets import Bbf
        return Bbf(self.finite_quadratic_module(), m)

    #@cached_method
    def C(self, m, unique=False):
        r'''
          Computes the C-Set of this genus symbol.

          INPUTS:
          - m: an integer, currently assumed to be prime.
          - unique: boolean, return only non-isomorphic modules.

          ALGORITHM:

            See [BEF].
        '''
        CS = C(self, m)
        if unique:
            CU = []
            for s in CS:
                cont = False
                for t in CU:
                    if t.defines_isomorphic_module(s):
                        cont = True
                if not cont:
                    CU.append(s)
            CS = CU
        return CS

    def _test_C(self, m, all=False):
        r"""
          Test the implementation of the C-sets


          INPUTS:
          - m: an integer
          - all: bool,
                 - if False, we check if all modules in C(A,m)
                   are actually contained in B(A,m),
                   by checking if they are obtained as a quotient.
                 - if True, we check if $C(A,m) \subset B(A,m)$
                   using the brute-force implementation of B(A,m).
                   We also check correctness for $p=2$
                   and level $2, 4, 8$.
                   

          OUTPUT:
          
            Returns True, if the test succeeded, otherwise False.
        """
        CS = self.C(m)
        M = self.finite_quadratic_module()
        if not all:
            for s in CS:
                N = s.finite_quadratic_module()
                q = False
                for G in N.subgroups():
                    if G.is_isotropic() and G.order() == m:
                        if (N / G).is_isomorphic(M):
                            q = True
                if not q:
                    print "Ooops, this one seems to be wrong: ", s
                return False
        else:
            BS = self.B(m)
            print BS
            print len(BS), len(CS)
            if self.level() in [2, 4, 8] and self.p_rank(2) <= 3:
                if len(BS) > len(CS):
                    print 'Missing symbols!'
                    return False
            for c in CS:
                found_isomorphic = False
                for b in BS:
                    if b.defines_isomorphic_module(c):
                        found_isomorphic = True
                        break
                if not found_isomorphic:
                    print c, " is not isomorphic to any module in s.B(" + str(m) + ")!"
                    return False

        return True

    def _from_string(self, s, debug = 0):
        r'''
           Initializes a GenusSymbol from a string.
           Most parts are copied from finite_quadratic_module.py
           in psage. This should be made work nicely together instead.
        '''
        sl = s.split('.')
        d = dict()
        for s in sl:
            L1 = s.split('^')
            if debug > 0: print L1
            if len(L1) > 2:
                raise ValueError()
            elif len(L1) == 1:
                nn = 1
            else:
                nn = L1[1]
            n = Integer(nn)
            L1 = L1[0].split("_")
            q = Integer(L1[0])
            if len(L1) > 2:  # more than one _ in item
                raise ValueError
            elif len(L1) == 2:
                if Integer(L1[1]) in range(8):
                    t = Integer(L1[1])
                else:
                    raise ValueError, "Type given, which ist not in 0..7: %s" % (
                        L1[1])
            else:
                t = None
            if not (n != 0 and q != 1 and q.is_prime_power()
                    and (None == t or (is_even(q) and t % 2 == n % 2))
                    and (not (None == t and is_even(q)) or 0 == n % 2)
                    ):
                raise ValueError, "{0} is not a valid signature!".format(s)
            p = q.prime_factors()[0]
            r = q.factor()[0][1]
            eps = sign(n)
            n = abs(n)
            if not d.has_key(p):
                d[p] = list()

            c = None
            if p == 2:
                c = None
                if t == None:
                    d[p].append([r, n, eps, 0, 0])
                else:
                    d[p].append([r, n, eps, 1, t % 8])
            else:
                d[p].append([r, n, eps])
        self._symbol_dict = d
        if not self._is_valid():
            raise ValueError

    def _is_valid(self):
        r"""
          Determines if the _symbol_dict dictionary actually defines
          a finite quadratic module.
        """
        for p, l in self._symbol_dict.iteritems():
            if not is_prime(p):
                return False
            if p != 2:
                if not isinstance(l, list):
                    return False
                for s in l:
                    if not isinstance(s, list) or len(s) != 3:
                        return False
                    r, n, eps = s
                    if not eps in [1, -1]:
                        return False
        if not self._symbol_dict.has_key(2):
            return True
        for r, n, eps, tp, t in self._symbol_dict[2]:
            # print r,n,eps,tp,t
            if tp == None:
                tp = 0
            if tp == 0 and n % 2 == 1:
                raise ValueError("Not a valid signature!")
            c = None
            if not t in range(8):
                return False
            if t == None or t == 0:
                if not is_even(n):
                    return False
            if tp == 0 and t != 0:
                return False
            if tp != 0:
                if 1 == n:
                    if not eps * n == kronecker(t, 2):
                        return False
                if n > 1:
                    c = None
                    CP = eval(
                        "cartesian_product([" + "[1,3,5,7]," * (n - 1) + "])")
                    # TODO: find better algorithm
                    for x in CP:
                        s = sum(x) % 8
                        if kronecker(prod(x) * (t - s), 2) == eps:
                            c = list(x)
                            #c.append(t - s)
                            break
                    # print "c=", c
                    if c is None:
                        return False
        return True

    def _to_string(self):
        if self._symbol_dict == {}:
            return '1^+1'
        symstr = ''
        for p, lsym in sorted(self._symbol_dict.iteritems()):
            for s in lsym:
                if s[0] == 0:
                    continue
                if len(symstr) != 0:
                    symstr = symstr + '.'
                symstr = symstr + str(p ** s[0])
                if p == 2:
                    sgn = '+' if s[2] == 1 else '-'
                    if s[3] == 1:
                        symstr = symstr + '_' + str(s[4])
                    symstr = symstr + '^' + sgn + str(s[1])
                    # else:
                    #    symstr = symstr + '^' + str(s[1])
                else:
                    sgn = '+' if (s[2] == 1) else '-'
                    symstr = symstr + '^' + sgn + str(s[1])
        return symstr

    def _reduce(self):
        sym = self._symbol_dict
        for p, sl in sym.iteritems():
            for s in sl:
                if s[1] == 0:
                    sl.remove(s)
                if s[0] == 0:
                    sl.remove(s)
            if p != 2:
                sl.sort()
                for s in sl:
                    # print s
                    ssl = copy(sl)
                    for j in range(sl.index(s) + 1, len(ssl)):
                        t = ssl[j]
                        if s[0] == t[0]:
                            s[1] = s[1] + t[1]
                            s[2] = s[2] * t[2]
                            sl.remove(t)
            else:
                sl.sort()
                for s in sl:
                    # print s
                    ssl = copy(sl)
                    for j in range(sl.index(s) + 1, len(ssl)):
                        t = ssl[j]
                        if s[0] == t[0]:
                            # print s, t
                            if s[3] == None:
                                s[3] = 0
                            if t[3] == None:
                                t[3] = 0
                            s[1] = s[1] + t[1]
                            s[2] = s[2] * t[2]
                            if s[3] != t[3]:
                                s[3] = 1
                                s[4] = t[4] if t[3] == 1 else s[4]
                            else:
                                s[4] = (s[4] + t[4]) % 8
                            # print s
                            sl.remove(t)
                # print sym

    def __repr__(self):
        return "Genus symbol " + self._to_string()

    def __str__(self):
        return self._to_string()

    def __add__(self, other):
        d = deepcopy(self._symbol_dict)
        e = other._symbol_dict
        for p, l in e.iteritems():
            if not d.has_key(p):
                d[p] = deepcopy(e[p])
            else:
                d[p] = deepcopy(d[p] + e[p])
        # print "in add: ", d_new
        s = GenusSymbol(d)
        s._reduce()
        return s

    def __sub__(self, other):
        r"""
          Try to formally 'subtract' ```other``` (B) from ```self``` (A).
          That is, check if
          \[
            A = B \oplus C
          \]
          holds for some finite quadratic module $C$ and if this is the case,
          returns $C$.

          Otherwise, returns an error.
        """
        debug = 0
        # print "In sub"
        err = ValueError("Result does not define a genus symbol")
        # print "in sub"
        # print "self = ", self, " other = ", other
        s = GenusSymbol(deepcopy(self._symbol_dict))
        # print "s = ", s
        s._reduce()
        d = s._symbol_dict
        e = other._symbol_dict
        # print d, e
        for p, l in e.iteritems():
            if not d.has_key(p):
                raise err
            else:
                for c in e[p]:
                    # print c
                    try:
                        j = s.jordan_component(p ** c[0])._symbol_dict[p]
                        # print j
                    except:
                        raise err
                    if not len(j) == 1:
                        raise ValueError("Strange error...")
                    else:
                        j = j[0]
                    if not j[1] - c[1] >= 0:
                        raise err
                    else:
                        if j[1] == c[1] and not j[2] == c[2]:
                            # same multiplicity, different eps
                            if debug > 0:
                                print 'same multiplicity, different eps'
                            if not (p == 2 and j[0] == 1 and j[4] == (c[4] + 4) % 8 and j[3] == c[3]):
                                raise err
                        if p == 2:
                            if j[1] == c[1]:
                                # same multiplicity
                                if not j[3] == c[3]:
                                    # different types
                                    raise err
                                if not j[4] == c[4]:
                                    # different oddity
                                    if debug > 0:
                                        print 'same multiplicity, different oddity'
                                    if not (j[0] == 1 and j[4] == (c[4] + 4) % 8 and j[2] != c[2] and j[3] == c[3]):
                                        # q=2, oddity differs by 4 and sign has
                                        # changed is ok.
                                        if debug > 0:
                                            print j[0], (j[4] == (c[4] + 4) % 8), (j[2] != c[2], j[2], c[2]), (j[3] == c[3])
                                        raise err
                            # print j[4], c[4], j,c
                            j[4] = (j[4] - c[4]) % 8
                            # print j[4]
                        j[2] = j[2] * c[2]
                        j[1] = j[1] - c[1]
        # print s
        s._reduce()
        if not s._is_valid():
            raise err
        return s

    def __eq__(self, o):
        r"""
          Check for equality by using the string representation.

          NOTE:
          This does not check for isomorphy.
        """
        if str(self) == str(o):
            return True
        else:
            return False

    def __le__(self, o):
        r"""
          Compare two genus symbols for ordering.
        """
        if self.level() > o.level():
            return False
        if self.order() > o.order():
            return False
        l = self._symbol_dict
        m = o._symbol_dict
        for p in sorted(l.keys()):
            if p in m.keys():
                for i in range(min(len(m[p]), len(l[p]))):
                    if l[p][i][0] > m[p][i][0]:
                        return False
                    if l[p][i][0] == m[p][i][0]:
                        if l[p][i][1] > l[p][i][1]:
                            return False
                        elif l[p][i][2] < m[p][i][2]:
                            return False
        return True
        #return str(self) <= str(o)

    def __lt__(self, o):
        r"""
          Compare two genus symbols for ordering.
        """
        if self.level() > o.level():
            return False
        if self.order() > o.order():
            return False
        l = self._symbol_dict
        m = o._symbol_dict
        for p in l.keys():
            if p in m.keys():
                for i in range(min(len(m[p]), len(l[p]))):
                    if l[p][i][0] >= m[p][i][0]:
                        if l[p][i][0] == m[p][i][0]:
                            if l[p][i][1] > m[p][i][1]:
                                return False
                            elif l[p][i][1] == m[p][i][1] and l[p][i][2] < m[p][i][2]:
                                return False
                        else:
                            return False
                    else:
                        return True
        return True

    def __hash__(self):
        r"""
          We use the string representation for hasing.
        """
        # if not hasattr(self,'_hash') or self._hash == None:
        self._reduce
        #l = map(lambda x: (x[0],tuple(map(lambda y: tuple(y),x[1]))),list(self._symbol_dict.iteritems()))
        #self._hash = hash(tuple(l))
        # return hash(tuple(l))
        return hash(str(self))

    def latex(self):
        r"""
          Returns a latex representation of ```self```.
        """
        o = r'$'
        l = str(self).split('.')
        for s in l:
            ss = s.split('^')
            if len(ss) == 2:
                s1, s2 = ss
            else:
                s1 = ss[0]
                s2 = '+1'
            o = o + s1 + r'^{' + s2 + r'}'
        o = o + r'$'
        return LatexExpr(o)


@cached_function
def C(genus_symbol, m, use_isomorphisms=True):
    r"""
      Return the set C(genus_symbol, m) as defined in [BEF].
    """
    m = Integer(m)
    
    Cs = list()
    if not is_prime(m):
        p = m.prime_factors([0])
        rec = True
    else:
        rec = False
        p = m

    # print "in C", genus_symbol
    Cs = Cs + trivial_rule(genus_symbol, p)
    if genus_symbol.p_rank(p) == 0:
        if not rec:
            return Cs
        else:
            sum(C(s,n) for s in Cs)

    # print Cs
    if p == 2:
        Cs = Cs + two_power_up_rules(genus_symbol)
        Cs = Cs + two_level_4_rules(genus_symbol)
        if use_isomorphisms and genus_symbol.p_rank(2)==3 and genus_symbol.values()[0]>1 and genus_symbol.signature() % 2 == 1:
            j2 = genus_symbol.jordan_component(2)+genus_symbol.jordan_component(4)
            s = j2.signature()
            if s % 2 == 1:
                l = [GenusSymbol("2_0^2.4_{0}^{1}".format(s, 1 if s % 8 in [1,7] else -1)), GenusSymbol("2_2^2.4_{0}^{1}".format((s-2) % 8, 1 if (s-2) % 8 in [1,7] else -1)), GenusSymbol("2_6^2.4_{0}^{1}".format((s-6) % 8, 1 if (s-6) % 8 in [1,7] else -1))]
                if j2 in l:
                    l.remove(j2)
                    for t in l:
                        Cs = Cs + C((genus_symbol - j2) + t,2,use_isomorphisms=False)
    else:
        Cs = Cs + odd_power_up_rules(genus_symbol, p)
    if not rec:
        return Cs
    else:
        return sum(C(s,n) for s in Cs)


def two_level_4_rules(genus_symbol):
    if genus_symbol.p_rank(2) == 0:
        return []
    J = genus_symbol.jordan_components(2)
    Bs = []
    for s in J:
        if s.valuation(2) == 1:
            try:
                # E4
                # print "E4"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, 1, 0, 0]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, 1, 1, 0]]})
                Bs.append(sym_new)
            except ValueError:
                pass
            try:
                # E5
                # print "E5"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, -1, 0, 0]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, -1, 1, 4]]})
                Bs.append(sym_new)
            except ValueError:
                pass
            try:
                # E6.1
                # print "E6.1"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, 1, 1, 2]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, 1, 1, 2]]})
                Bs.append(sym_new)
            except ValueError:
                pass
            try:
                # E6.2
                # print "E6.2"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, 1, 1, 6]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, 1, 1, 6]]})
                Bs.append(sym_new)
            except ValueError:
                pass
            try:
                # E7.1
                # print "E7.1"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, 1, 1, 2]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, -1, 1, 2]]})
                Bs.append(sym_new)
            except ValueError:
                pass
            try:
                # E7.2
                # print "E7.2"
                sym_new = genus_symbol - GenusSymbol({2: [[1, 2, 1, 1, 6]]})
                sym_new = sym_new + GenusSymbol({2: [[2, 2, -1, 1, 6]]})
                Bs.append(sym_new)
            except ValueError:
                pass
    return Bs


def two_power_up_rules(genus_symbol):
    if genus_symbol.p_rank(2) == 0:
        return []
    J = genus_symbol.jordan_components(2)
    Bs = []
    for s in J:
        # print s
        try:
            # E1
            # print "E1"
            sym_new = genus_symbol - \
                GenusSymbol({2: [[s.valuation(2), 2, 1, 0, 0]]})
            # print 'sym_new', sym_new
            sym_new1 = sym_new + \
                GenusSymbol({2: [[s.valuation(2) + 1, 2, 1, 0, 0]]})
            Bs.append(sym_new1)
            # print sym_new, J
        except ValueError:
            pass
        try:
            # E2
            # print "E2"
            sym_new = genus_symbol - \
                GenusSymbol({2: [[s.valuation(2), 2, -1, 1, 4]]})
            # print 'sym_new', sym_new
            sym_new1 = sym_new + \
                GenusSymbol({2: [[s.valuation(2) + 1, 2, -1, 0, 0]]})
            Bs.append(sym_new1)
            # print sym_new, J
        except ValueError:
            pass
        # And now E3
        for o in [1, 3, 5, 7]:
            # print "trying o = %d for s = %s"%(o,s)
            try:
                # E3
                # print "E3:", genus_symbol
                s1 = GenusSymbol(
                    {2: [[s.valuation(2), 1, kronecker(o, 2), 1, o]]})
                # print s1
                sym_new = genus_symbol - s1
                # print genus_symbol
                # print 'sym_new', sym_new
                sym_new1 = sym_new + \
                    GenusSymbol(
                        {2: [[s.valuation(2) + 2, 1, kronecker(o, 2), 1, o]]})
                # print genus_symbol
                Bs.append(sym_new1)
                # print sym_new, J
            except ValueError:
                pass
            # print "Done, first part"
    return Bs


def odd_power_up_rules(genus_symbol, p):
    if not is_odd(p) or not is_prime(p):
        raise ValueError
    Bs = []
    if genus_symbol.p_rank(p) == 0:
        return Bs
    J = genus_symbol.jordan_components(p)
    for s in J:
        # print s
        try:
            sym_new = genus_symbol - GenusSymbol({p: [[s.valuation(p), 1, 1]]})
            sym_new1 = sym_new + GenusSymbol({p: [[s.valuation(p) + 2, 1, 1]]})
            Bs.append(sym_new1)
        except:
            pass
        try:
            sym_new = genus_symbol - \
                GenusSymbol({p: [[s.valuation(p), 1, -1]]})
            sym_new1 = sym_new + \
                GenusSymbol({p: [[s.valuation(p) + 2, 1, -1]]})
            Bs.append(sym_new1)
        except:
            pass
        try:
            sym_new = genus_symbol - GenusSymbol({p: [[s.valuation(p), 2, 1]]})
            sym_new1 = sym_new + \
                GenusSymbol({p: [[s.valuation(p) + 1, 2, ep]]})
            Bs.append(sym_new1)
        except:
            pass
        try:
            sym_new = genus_symbol - \
                GenusSymbol({p: [[s.valuation(p), 2, -1]]})
            sym_new1 = sym_new + \
                GenusSymbol({p: [[s.valuation(p) + 1, 2, -ep]]})
            Bs.append(sym_new1)
        except:
            pass
    return Bs


def trivial_rule(s, p):
    r"""
      Apply the 'trivial' rules to $s$ for the prime $p$,
      that is the rules that are of the form $1^+1 \# mapsto A$
      for a finite quadratic module $A$ of order $p^2$.
    """
    p = Integer(p)
    if not is_prime(p):
        raise ValueError("p={0} has to be a prime number.".format(p))
    if p == 2:
        sp2 = GenusSymbol("2^+2")
        so2 = GenusSymbol("2_0^+2")
        s1 = s + sp2
        s2 = s + so2
        if not s1 == s2:
            return [s1, s2]
        else:
            return [s1]
    else:
        ep = -1 if p % 4 == 3 else 1
        sp = []
        sp.append(GenusSymbol(str(p) + "^" + str(ep * 2)))
        sp.append(GenusSymbol(str(p ** 2) + "^+1"))
        sp.append(GenusSymbol(str(p ** 2) + "^-1"))
        return [s + _ for _ in sp]


@cached_function
def prime_anisotropic_symbols(p, fake=False):
    r"""
      Return a list of all anisotropic symbols of prime level $p$.

      INPUTS:
       - p: A prime number or equal to 1
       - fake: Do not return all symbols,
               but just $p^+1$ and $p^+2$ for odd $p$,
               $1^+1$ for $p = 1$
               and similar for $p = 4$ and $p = 8$.
               This is used to just reflect the possible structures
               of the corresponding finite abelian groups.
    """
    p = Integer(p)
    
    if not (p == 1 or is_prime(p) or p in [4, 8]):
        return []
    else:
        if is_odd(p) and is_prime(p):
            if fake:
                l = [str(p) + '^+1', str(p) + '^+2']
            else:
                if p % 4 == 3:
                    l = [str(p) + '^+1', str(p) + '^-1', str(p) + '^+2']
                else:
                    l = [str(p) + '^+1', str(p) + '^-1', str(p) + '^-2']
        else:
            if p == 1:
                l = ['1^+1']
            elif p == 2:
                l = ['2^-2']
            elif p == 4:
                if fake:
                    l = ['2_1^+1', '2_2^+2', '2_3^+3']
                else:
                    # TODO: are these correct?? (2_6^+2, 2_5^+3 sollte hier
                    # nicht stehen!?!?)
                    l = [
                        '2_1^+1', '2_7^+1', '2_2^+2', '2_6^+2', '2_3^+3', '2_5^+3']
            elif p == 8:
                if fake:
                    l = ['4_1^+1', '2_1^+1.4_1^+1']
                else:
                    l = ['4_1^+1', '4_3^-1', '4_5^-1', '4_7^+1', '2_1^+1.4_1^+1',
                         '2_1^+1.4_3^-1', '2_1^+1.4_5^-1', '2_1^+1.4_7^+1']
        # print l
        return map(lambda x: GenusSymbol(x), l)


@cached_function
def anisotropic_symbols(N, sig=None, fake=False):
    r"""
      Return a list of all anisotropic symbols of given level and signature.
      If ```fake``` is True, then only return all possible structures
      of finite abelian groups.
    """
    N = Integer(N)
    if sig != None and fake == True:
        raise ValueError(
            "You provided a signature and requested fake symbols. This does not make any sense.")
    syms = []
    if N == 1:
        if (sig == None or sig % 8 == 0):
            return prime_anisotropic_symbols(1)
        else:
            return []
    if is_prime_power(N):
        syms = prime_anisotropic_symbols(N, fake=fake)
    else:
        p = max(N.prime_factors())
        M = N / p
        q = p ** N.valuation(p)
        syms = anisotropic_symbols(M)
        syms = syms = map(lambda r: r[
                          0] + r[1], itertools.product(syms, prime_anisotropic_symbols(q, fake=fake)))
    if not sig == None:
        syms = filter(lambda s: s.signature() == sig, syms)
    have = []
    syms_new = []
    return syms


def gamma0_N_genus_symbol(N):
    s = GenusSymbol()
    # print s
    N = Integer(2 * N)
    for p in N.prime_factors():
        # print s, p
        if p == 2:
            v = N.valuation(2)
            # print v
            gs = str(2 ** (v)) + "_" + str((N / 2 ** v) % 8) + "^" + \
                ("+1" if kronecker(N / 2 ** v, 2) == 1 else "-1")
            # print gs
            g = GenusSymbol(gs)
            s = s + g
        else:
            v = N.valuation(p)
            Np = p ** v
            np = N / Np
            gs = str(Np) + "^" + ("+1" if kronecker(np, p) == 1 else "-1")
            # print gs
            s = s + GenusSymbol(gs)
    return s

def gamma1_genus_symbol(N):
    N = Integer(N)
    return GenusSymbol(FiniteQuadraticModule([2,N,N],[1/Integer(4),0,0,0,1/N,0]).jordan_decomposition().genus_symbol())

def t1_genus_symbol(a,N):
    a = Integer(a)
    N = Integer(N)
    return GenusSymbol(FiniteQuadraticModule([2*a,N,N],[1/(4*a),0,0,0,1/N,0]).jordan_decomposition().genus_symbol())
