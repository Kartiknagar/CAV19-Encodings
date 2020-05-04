;Encoding of NON-INTERF-1

;Datatype declaration
;Coming from the CRDT
(declare-sort T);Elements of the set
(declare-sort S);Set
(declare-datatypes () ((OpType (A) (R) )));Type of Operation

;Coming from the Verification Framework
(declare-sort E);Event
(declare-sort I);Event-Ids

;Functions and Predicates
(declare-fun op (E) OpType)
(declare-fun arg (E) T)
(declare-fun src (E) S)
(declare-fun eid (E) I)

(declare-fun eo (E E) Bool);Effector order
(declare-fun vis (E E) Bool);Visibility Relation
(declare-const s0 S);Init CRDT State


;Set CRDT Encoding
(declare-fun c (S T) Bool)
(declare-fun add (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (add s3 s1 a s2) (= (c s2 x) (ite (= x a) true (c s1 x) ) ) ) ))

(declare-fun remove (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (remove s3 s1 a s2) (= (c s2 x) (ite (= x a) false (c s1 x) ) ) ) ))

;To encode NON-INTERF-1, we instantiate two events beginning from the initial CRDT state which do not commute modulo \Psi, which we express by applying the effectors of the two events in both orders and asserting the they lead to different states, provided that the consistency policy allows both orderings.
(declare-const e1p E)
(declare-const e2p E)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (= (src e1p) s0) ))
(assert (=> (not (vis e1p e2p))  (= (src e2p) s0) ))

(declare-fun apply (E S S) Bool)
(assert (forall ((e E)(s1 S)(s2 S)) (= (apply e s1 s2) (ite (= (op e) A) (add (src e) s1 (arg e) s2) (remove (src e) s1 (arg e) s2) ) ) ))

(assert (=> (vis e2p e1p) (apply e2p s0 (src e1p))   ) )
(assert (=> (vis e1p e2p) (apply e1p  s0 (src e2p))   ) )

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
 (assert (not (= pe11 pe12)))

(assert (apply pe11 s0 se11) )
(assert (apply pe12 se11  se12) )
(assert (eoe1 pe11 pe12))
(assert (not (eoe1 pe12 pe11)))

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
 (assert (not (= pe21 pe22)))

(assert (apply pe21 s0 se21))
(assert  (apply pe22 se21  se22) )
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))

 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (c se12 a) (c se22 a))))

;Consistency Policy - PSI+RB
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) (= (op e1) A) (= (op e2) A) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis x1 x2) (vis x2 x3)) (vis x1 x3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (eo e1 e2) ) ))


(check-sat)
(get-model)
