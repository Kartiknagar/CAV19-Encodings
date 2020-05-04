
The artifact consists of First-order logic encodings of the Verification Conditions generated using Def. 7 (Non-interference to Commutativity, Page-11) in the paper, written in Z3's input format.

To run the individual encodings, simply execute z3 using the -smt2 option. For example, to run the encoding 'Set_EC_base.smt' use the following command:

z3 -smt2 Set/Set_EC_base.smt 

--------------
Output
--------------

The encodings basically encode the negation of the VCs as described in Def. 7 (explained in more detail in the Experimental Results Section in the paper, Page-13). There are two VCs (corresponding to the two conditions in Def. 7), which we call as NON-INTERF-1 and NON-INTERF-2, and encoded as xx_yy_base.smt and xx_yy_inductive.smt, where xx is the CRDT and yy is the consistency policy. 

If Z3 returns SAT on either VC, then the VC is violated, and we return the output as 'xx fails NON-INTERF-Z under yy'. Refering to the table in Fig. 4 (Page-14) in the paper, this corresponds to a cross-mark. On the other hand, if Z3 returns UNSAT on both the VCs, then we return the output as 'xx converges under yy'. This corresponds to a check-mark in the table. We check the validity of NON-INTERF-2 only if NON-INTERF-1 is valid.

Note that Z3 takes slightly longer time to determine the satisfiability of encodings for graph-orset (~1 minute).

As indicated in the paper (Page-15, last paragraph), except for 'uset', whenever a CRDT fails NON-INTERF under a consistency policy, it fails NON-INTERF-1, which corresponds to a concrete convergence violation. For 'uset' under 'CC', NON-INTERF-1 passes but NON-INTERF-2 fails. However, we can analyze the satisfying model returned by Z3 to construct an actual convergence violation involving three events.


---------------
Explanation
---------------

For every combination of CRDT and consistency policy, we encode the VCs (NON-INTERF-2 is encoded only if NON-INTERF-1 is shown to be valid). All the encodings follow the same format : encoding the CRDT operations followed by encoding of the actual VC followed by encoding of the consistency policy. Detailed comments on the encoding of the two VCs can be found in the files : z3-scripts/simpleset/simpleset_EC_base.smt and z3-scripts/simpleset/simpleset_PSI_inductive.smt.

The encoding of the VC is almost same across all CRDTs (so for example, xx_yy_base.smt has the same encoding of the VC across all xx and yy), with some minor changes depending on the number of operations and signature of operations of the CRDT. 

The encoding of the CRDT is the same across all VCs and all consistency policies (so for example, xx_yy_zz.smt has the same encoding of CRDT for all yy and zz).

The encoding of the consistency policy is the same across all CRDTs and VCs (so for example, xx_yy_zz.smt has the same encoding of the consistency policy for all xx and zz), with minor changes for the consistency policy PSI+RB whose encoding depends on the operations of the CRDT.

Note that one can comment out the consistency policy in any existing file and add the encoding of another consistency policy to observe the same results.

If Z3 returns SAT on any of the encodings, then it means that the VC is violated, and the satisfying model returned by Z3 can be analyzed to pinpoint the CRDT operations and the exact execution resulting in a convergence violation. 

Finally, our approach can be directly applied to newer CRDTs and consistency policies by simply replacing the relevant portions in any of the given encodings with the encoding of the new CRDT and/or the consistency policy. 

