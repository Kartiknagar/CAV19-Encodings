; Encoding of NON-INTERF-2

; Declaration of the various un-interpreted datatypes used in the encoding. We divide these into two parts : (1) Datatypes used in the CRDT definition and (2) Datatypes used for the Verification framework. (2) remains the same in all encodings, only (1) changes depending upon the CRDT.

; Across all encodings, we always use T for the element datatype (to be stored in the set), S for the set datatype, E for the event datatype and I for the event-id datatype.


; Coming from the CRDT
(declare-sort T) ;Elements of the set
(declare-sort S) ;Set
(declare-datatypes () ((OpType (A) (R) ))) ;Type of operation. For the Set CRDT only two types : Add and Remove

; Coming from the verification framework
(declare-sort E) ;Event
(declare-sort I) ;Event-id

; Functions and Predicates
(declare-fun op (E) OpType) ;Type of CRDT operation performed by an event
(declare-fun arg (E) T) ;Argument of CRDT operation performed by an event
(declare-fun src (E) S) ;Source state of the replica on which the event is called
(declare-fun eid (E) I) ;Event-id

;Set CRDT Encoding
(declare-fun c (S T) Bool) ;Contains predicate - True if element belongs to the set, False otherwise

;The encoding essentially constrains the contains predicate when an element is added or removed. When an element is added, the newly added element and all the elements in the input set must be contained in the output set. When an element is removed, the newly removed element must not be present in the output set, but all other elements present in the input set must remain in the output.
;Below, s1 is source replica state, s2 is the input replica state s3 is the output replica state.
(declare-fun add (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (add s3 s1 a s2) (= (c s2 x) (ite (= x a) true (c s1 x) ) ) ) ))

(declare-fun remove (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (remove s3 s1 a s2) (= (c s2 x) (ite (= x a) false (c s1 x) ) ) ) ))

;The following portion encodes the verification condition and is common across all encodings

;We first encode the antecedent of NON-INTERF-2. Here, we need to encode executions with two events such that both events commute modulo /Psi.
;\eta_1 : e1
;\eta_2 : e2
;\sigma_1 : ss1
;\sigma_2 : ss2

(declare-const s0 S)
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(assert (not (= e1 e2)))


(declare-fun vis1 (E E) Bool)
(assert  (ite (vis1 e1 e2) (ite (= (op e1) A) (add (src e1) ss2 (arg e1) (src e2)) (remove (src e1) ss2 (arg e1) (src e2)) ) (= (src e2) ss2) ))
(assert  (ite (vis1 e2 e1) (ite (= (op e2) A) (add (src e2) ss1 (arg e2) (src e1)) (remove (src e2) ss1 (arg e2) (src e1)) ) (= (src e1) ss1) ))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)

;To check for commutativity modulo \Psi, we apply the effectors of the two events in two orders and compute the resulting final states (s12 and s22), capturing the two orders by eo1 and eo2. Then, if the consistency model \Psi allows both the effector orders eo1 and eo2, both the states s12 and s22 must be equal, capturing their commutativity.

(declare-const s11 S)
(declare-const s12 S)

(assert (ite (= (op e1) A) (add (src e1) s0 (arg e1) s11) (remove (src e1) s0 (arg e1) s11) ))
(assert (ite (= (op e2) A) (add (src e2) s11 (arg e2) s12) (remove (src e2) s11 (arg e2) s12) ))
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)

(assert (ite (= (op e2) A) (add (src e2) s0 (arg e2)  s21) (remove (src e2) s0 (arg e2) s21) ))
(assert (ite (= (op e1) A) (add (src e1) s21 (arg e1) s22) (remove (src e1) s21 (arg e1) s22) ))
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))


(assert (forall ((t T)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2))) (=> (= (arg e1) (arg e2)) (or (vis1 e1 e2) (vis1 e2 e1)) ) (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (= (c s12 t) (c s22 t)) )))


;Finally, we encode the consequent of NON-INTERF-2 by asking for an execution involving a third interfering event which breaks the commutativity (modulo \Psi) of the two previous events. We use the same strategy for encoding as used above by performing the two events in two different orders and encoding that they result in two different states and the two orders are allowed by the consistency policy

(declare-const e3 E)
(declare-const ss3 S)
(declare-const e1p E)
(declare-const e2p E)
(assert (= (op e1) (op e1p)))
(assert (= (op e2) (op e2p)))
(assert (= (arg e1) (arg e1p)))
(assert (= (arg e2) (arg e2p)))
(assert (= (eid e1) (eid e1p)))
(assert (= (eid e2) (eid e2p)))
(assert (not (= e1p e3)))
(assert (not (= e2p e3)))

(declare-fun eo (E E) Bool)
(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))


(assert (= (vis1 e1 e2) (vis e1p e2p) ))
(assert (= (vis1 e2 e1) (vis e2p e1p) ))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (= (src e1p) ss1) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (= (src e2p) ss2) ))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (ite (= (op e3) A) (add (src e3) ss1 (arg e3)  (src e1p)) (remove (src e3) ss1 (arg e3) (src e1p))  )   ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (ite (= (op e2p) A) (add (src e2p) ss1 (arg e2p)  (src e1p)) (remove (src e2p) ss1 (arg e2p) (src e1p))  )   ) )
(assert (exists ((ns S))(=> (and (vis e3 e1p) (vis e2p e1p)) (and (ite (= (op e3) A) (add (src e3) ss1 (arg e3)  ns) (remove (src e3) ss1 (arg e3) ns)  ) (ite (= (op e2p) A) (add (src e2p) ns (arg e2p)  (src e1p)) (remove (src e2p) ns (arg e2p) (src e1p))  ) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (ite (= (op e3) A) (add (src e3) ss2 (arg e3)  (src e2p)) (remove (src e3) ss2 (arg e3) (src e2p))  )   ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p)) (ite (= (op e1p) A) (add (src e1p) ss2 (arg e1p)  (src e2p)) (remove (src e1p) ss2 (arg e1p) (src e2p))  )   ) )
(assert (exists ((ns S))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (ite (= (op e3) A) (add (src e3) ss2 (arg e3)  ns) (remove (src e3) ss2 (arg e3) ns)  ) (ite (= (op e1p) A) (add (src e1p) ns (arg e1p)  (src e2p)) (remove (src e1p) ns (arg e1p) (src e2p))  ) )  ) ))


(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-fun next1 (E E) Bool)

(assert (or (= pe11 e1p) (= pe11 e2p)))
(assert (or (= pe12 e1p) (= pe12 e2p)))
(assert (forall ((e E)) (or (= e pe11) (eoe1 pe11 e)) ))


(assert (ite (= (op pe11) A) (add (src pe11) s0 (arg pe11)  se11) (remove (src pe11) s0 (arg pe11) se11) ))
(assert (ite (= (op pe12) A) (add (src pe12) se11 (arg pe12)  se12) (remove (src pe12) se11 (arg pe12) se12) ))
(assert (next1 pe11 pe12))

(assert (forall ((e1 E) (e2 E) (e E)) (=> (next1 e1 e2) (and (eoe1 e1 e2) (=> (eoe1 e1 e) (or (= e2 e) (eoe1 e2 e) ) ) )) ))
(assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe1 e1 e2) (eoe1 e2 e3)) (eoe1 e1 e3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe1 e1 e2) (eoe1 e2 e1)) )))
(assert (forall ((e E)) (not (eoe1 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe1 e1 e2)) ))

(declare-const pe21 E)
(declare-const pe22 E)
(declare-fun next2 (E E) Bool)
(declare-fun eoe2 (E E) Bool)

(assert (or (= pe21 e1p) (= pe21 e2p)))
(assert (or (= pe22 e1p) (= pe22 e2p)))
(assert (forall ((e E)) (or (= e pe21) (eoe2 pe21 e)) ))


(assert (ite (= (op pe21) A) (add (src pe21) s0 (arg pe21)  se21) (remove (src pe21) s0 (arg pe21) se21) ))
(assert (ite (= (op pe22) A) (add (src pe22) se21 (arg pe22)  se22) (remove (src pe22) se21 (arg pe22) se22) ))
(assert (next2 pe21 pe22))

(assert (forall ((e1 E) (e2 E) (e E)) (=> (next2 e1 e2) (and (eoe2 e1 e2) (=> (eoe2 e1 e) (or (= e2 e) (eoe2 e2 e) ) ) )) ))
(assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (c se12 a) (c se22 a))))


;Consistency Policy - PSI
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) (vis e1 e2)) (eo e1 e2) ) ))


(check-sat)
(get-model)
