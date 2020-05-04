;Encoding of NON-INTERF-1

;Coming from the CRDT
(declare-sort T);Tuple
(declare-sort A);Element
(declare-sort S);Set
(declare-datatypes () ((OpType (A) (R) )))

;Coming from the verification framework
(declare-sort I);Identifier
(declare-sort E);Event

;Functions and Predicates
(declare-fun elem (T) A);Project element out of tuple
(declare-fun id (T) I);Project identifier out of tuple
(declare-fun op (E) OpType)
(declare-fun arg (E) A)
(declare-fun src (E) S)
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-fun vis (E E) Bool)
(declare-const s0 S)


;ORSet Encoding
(declare-fun c (S T) Bool)
(assert (forall ( (t1 T) (t2 T)) (=>  (= (id t1) (id t2))  (= t1 t2) ) ))
(declare-fun add (S S A I S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) )  (=> (and (add s3 s1 a i s2) (c s1 x)) (c s2 x) ) ))
(assert (forall ( (a A) (s1 S) (s2 S) (s3 S) (i I) ) (exists ((x T)) (=>  (add s3 s1 a i s2 ) (and (not (= s1 s2)) (c s2 x) (= (elem x) a) (= (id x) i) (not (c s1 x)) (not (c s3 x))) ) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) ) (=> (and (add s3 s1 a i s2) (c s2 x)) (or (c s1 x) (and (not (c s1 x)) (= (elem x) a) (= (id x) i))) ) ) )


(declare-fun remove (S S A S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) )  (=> (and (remove s3 s1 a s2 ) (c s3 x) (= (elem x) a) )(not (c s2 x)) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) )  (=> (and (remove s3 s1 a s2 ) (c s1 x) (not (= (elem x) a)) )  (c s2 x) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) )  (=> (and (remove s3 s1 a s2 ) (c s1 x)  (= (elem x) a) (not (c s3 x))  ) (c s2 x) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) )  (=> (and (remove s3 s1 a s2 ) (c s2 x)) (or (not (= (elem x) a)) (and (= (elem x) a)
  (not (c s3 x)) ) ) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) )  (=> (and (remove s3 s1 a s2 ) (c s2 x)) (c s1 x) ) ))

;Predicate to check whether an element is present in the ORSet
(declare-fun ca (S A) Bool)
(assert (forall ((s S) (a A) (x T) ) (=> (and (c s x) (= (elem x) a) ) (ca s a) ) ))
(assert (forall ((s S) (a A) ) (exists ((x T))  (=> (ca s a) (and (c s x) (= (elem x) a)) ) ) ))

;NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (= (src e1p) s0) ))
(assert (=> (not (vis e1p e2p))  (= (src e2p) s0) ))

(declare-fun apply (E S S) Bool)
(assert (forall ((e E)(s1 S)(s2 S)) (= (apply e s1 s2) (ite (= (op e) A) (add (src e) s1 (arg e) (eid e) s2) (remove (src e) s1 (arg e) s2) ) ) ))

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

(declare-const a A)
(assert  (not (= (ca se12 a) (ca se22 a))))

;Consistency Policy-PSI
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) (vis e1 e2)) (eo e1 e2) ) ))


(check-sat)
(get-model)
