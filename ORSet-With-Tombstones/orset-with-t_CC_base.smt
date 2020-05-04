;Encoding of NON-INTERF-1

;Coming from the CRDT
(declare-sort T);Tuple
(declare-sort A);Element
(declare-datatypes () ((OpType (A) (R) )))
(declare-sort S);Set

;Coming from the verification framework
(declare-sort I);Event-id, also works as identifier
(declare-sort E);Event

;Functions and Predicates
(declare-fun elem (T) A);Projecting element
(declare-fun id (T) I);Projecting identifier
(declare-fun op (E) OpType)
(declare-fun arg (E) A)
(declare-fun src (E) S);Set at source replica
(declare-fun srcr (E) S);Tombstone set at source replica
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-fun vis (E E) Bool)
(declare-const s0 S)
(declare-const s0r S)

(declare-fun c (S T) Bool)
(assert (forall ((a T)) (not (c s0 a)) ))
(assert (forall ((a T)) (not (c s0r a)) ))

(assert (forall ( (t1 T) (t2 T)) (=>  (= (id t1) (id t2))  (= t1 t2) ) ))

;ORSet with tombstones encoding
(declare-fun add (S S S S A I S S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) (i I) )  (=> (and (add s3 s3r s1 s1r a i s2 s2r) (c s1 x)) (c s2 x) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) (i I) )  (=> (and (add s3 s3r s1 s1r a i s2 s2r) (c s1r x)) (c s2r x) ) ))
(assert (forall ( (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) (i I) ) (exists ((x T)) (=>  (add s3 s3r s1 s1r a i s2 s2r ) (and (not (= s1 s2)) (= s1r s2r) (c s2 x)  (= (elem x) a) (= (id x) i) (not (c s1 x)) (not (c s1r x)) (not (c s3 x)) (not (c s3r x)) ) ) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) (i I) ) (=> (and (add s3 s3r s1 s1r a i s2 s2r) (c s2 x)) (or (c s1 x) (and (not (c s1 x)) (= (elem x) a) (= (id x) i))) ) ) )


(declare-fun remove (S S S S A S S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) )  (=> (and (remove s3 s3r s1 s1r a s2 s2r ) (c s3 x) (= (elem x) a) ) (c s2r x)) ) )
(assert (forall ( (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) )  (=> (remove s3 s3r s1 s1r a s2 s2r) (= s1 s2) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) )  (=> (and (remove s3 s3r s1 s1r a s2 s2r) (c s1r x)) (c s2r x) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (s1r S) (s2r S) (s3r S) )  (=> (and (remove s3 s3r s1 s1r a s2 s2r) (c s2r x)) (or (c s1r x)  (and (c s3 x) (= (elem x) a) )) ) ))

(declare-fun ca (S S A) Bool)
(assert (forall ((s S) (sr S) (a A) (x T) ) (=> (and (c s x) (not (c sr x)) (= (elem x) a) ) (ca s sr a) ) ))
(assert (forall ((s S) (sr S) (a A) ) (exists ((x T))  (=> (ca s sr a) (and (c s x) (= (elem x) a) (not (c sr x)) ) ) ) ))

;Encoding of NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (and (= (src e1p) s0) (= (srcr e1p) s0r)) ))
(assert (=> (not (vis e1p e2p))  (and (= (src e2p) s0) (= (srcr e2p) s0r) ) ))

(declare-fun apply (E S S S S) Bool)
(assert (forall ((e E)(s1 S)(s2 S)(s1r S)(s2r S)) (= (apply e s1 s1r s2 s2r) (ite (= (op e) A) (add (src e) (srcr e) s1 s1r (arg e) (eid e) s2 s2r) (remove (src e) (srcr e) s1 s1r (arg e) s2 s2r) ) ) ))

(assert (=> (vis e2p e1p) (apply e2p s0 s0r (src e1p) (srcr e1p))   ) )
(assert (=> (vis e1p e2p) (apply e1p  s0 s0r (src e2p) (srcr e2p))   ) )



(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-const se11r S)
(declare-const se12r S)
(declare-const se21r S)
(declare-const se22r S)
(declare-fun next1 (E E) Bool)

 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))

(assert (apply pe11 s0 s0r se11 se11r) )
(assert (apply pe12 se11 se11r  se12 se12r) )
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

(assert (apply pe21 s0 s0r se21 se21r))
(assert  (apply pe22 se21 se21r  se22 se22r) )
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))

 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a A)
(assert  (not (= (ca se12 se12r a) (ca se22 se22r a))))

;Consistency Policy-CC
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis x1 x2) (vis x2 x3)) (vis x1 x3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (eo e1 e2) ) ))

(check-sat)
(get-model)
