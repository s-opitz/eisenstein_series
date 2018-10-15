"""
Some functions to get Gram matrices or lmfdb labels for lattices from the L-functions and Modular Forms Database, http://www.lmfdb.org.

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

from urllib import urlopen, quote
from sage.misc.temporary_file import tmp_filename
from sage.repl.load import load
import re
from sage.all import Integer, matrix

def lmfdb_label(gram_matrix):
    l = []
    n = gram_matrix.nrows()
    for j in range(n):
        l.extend(gram_matrix.rows()[j][j:])
    gram_string = quote(str(l).replace(' ',''), '')
    url = 'http://www.lmfdb.org/Lattice/?start=0&dim=&det=&level=&gram={0}&minimum=&class_number=&aut=&count=1'.format(gram_string)
    u = urlopen(url)
    s = u.read()
    label = re.search(r'([0123456789]+\.){4}[0123456789]+', s).group()

    return label

def lmfdb_gram_matrix(label):
    n = Integer(label[:label.index('.')])
    url = 'http://www.lmfdb.org/Lattice/' + label
    u = urlopen(url)
    s = u.read()
    s = s[s.index('Gram Matrix'):]
    s = s[s.index(r'\begin{array}') : s.index(r'\end{array}')]

    nums = []
    for j in range(n**2):
        num = re.search('-?[0123456789]+', s).group()
        s = s[s.index(num) + len(num) :]
        nums.append(Integer(num))

    m = matrix(n,n,nums)
    
    return m

def lmfdb_genus_representatives(label):
    url = 'http://www.lmfdb.org/Lattice/' + label + '/download/sage/genus_reps'
    u = urlopen(url)
    s = u.read()
    with open(tmp_filename(ext='.sage'), 'w') as f:
        f.write(s)
    load(f.name, globals())
    return data
    
#link = 'http://www.lmfdb.org/Lattice/3.856.428.10.4/download/sage/genus_reps'
#data = lmfdb_genus_representatives(link)



