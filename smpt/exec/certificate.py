"""
Invariance Certificate Module

This file is part of SMPT.

SMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

SMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with SMPT. If not, see <https://www.gnu.org/licenses/>.
"""

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "5.0"


from os import remove, system
from tempfile import NamedTemporaryFile
from typing import Optional

from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import PetriNet

def certificate(ptnet: PetriNet, formula: Formula, certificate: str, k: Optional[int] = int, path: Optional[str] = None, check: bool = False) -> None:
    """ Write an invariance certificate in a file (with its checking assertions), and check if required. 
    """
    certificate_path = path if path is not None else NamedTemporaryFile(suffix='.aut', delete=False)
    
    with open(certificate_path, 'w') as fp:
        fp.write("(set-logic LIA)\n\n")
        fp.write("; Certificate\n\n")
        fp.write("(define-fun cert ({}) Bool {})\n".format(ptnet.smtlib_declare_places_as_parameters(k), certificate))
        
        fp.write("\n\n; Check\n\n")
        fp.write(ptnet.smtlib_declare_places(0))
        fp.write("\n")
        fp.write(ptnet.smtlib_declare_places(1))

        call_0, call_1 = ptnet.smtlib_call_places_as_parameters(0), ptnet.smtlib_call_places_as_parameters(1)

        fp.write('\n(echo "<> I => Cert (must be unsat)")\n')
        fp.write("(push)\n")
        fp.write('(assert (and {} (not (cert {}))))\n'.format(ptnet.smtlib_initial_marking_as_formula(0), call_0))
        fp.write("(check-sat)\n")
        fp.write("(pop)\n")

        fp.write('\n(echo "<> Cert /\ T => Cert\' (must be unsat)")\n')
        fp.write("(push)\n")
        fp.write('(assert (and (cert {}) {} (not (cert {}))))\n'.format(call_0, ptnet.smtlib_transition_relation_without_assertion(0), call_1))
        fp.write("(check-sat)\n")
        fp.write("(pop)\n")

        fp.write('\n(echo "<> Cert => Inv (must be unsat)")\n')
        fp.write('(assert (and (cert {}) {}))\n'.format(call_0, formula.R.smtlib(0)))
        fp.write("(check-sat)\n")
    
    if check:
        system("cvc5 --incremental {}".format(certificate_path))

    if path is None:
        remove(certificate_path)
