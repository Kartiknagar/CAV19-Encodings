;Encoding NON-INTERF-2

;Datatypes declaration
(declare-sort T)
(declare-sort S)
(declare-sort E)
(declare-sort I)
(declare-sort A)
(declare-datatypes () ((OpType (Add) (R) )))
(declare-fun op (E) OpType)
(declare-fun elem (T) A)
(declare-fun parent (T) T)
(declare-fun ts (T) I)
(declare-fun argE (E) T)
(declare-fun argN (E) A)
(declare-fun src (E) S)
(declare-fun srcr (E) S)
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-const s0 S)
(declare-const s0r S)


(declare-fun tso (I I) Bool)
(assert (forall ((t1 I) (t2 I) (t3 I)) (=> (and (tso t1 t2) (tso t2 t3)) (tso t1 t3) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (not (= t1 t2)) (or (tso t1 t2) (tso t2 t1)) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (tso t1 t2) (not (tso t2 t1)) ) ))

(assert (forall ( (t1 T) (t2 T)) (=>  (= (ts t1) (ts t2))  (= t1 t2) ) ))

;Encoding RGA CRDT
(declare-fun c (S T) Bool)
(declare-fun add (S S S S T A I S S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s1 y)) (c s2 y) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s3 y)) (tso (ts y) i) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=>  (add s3 s3r s1 s1r x a i s2 s2r) (and (not (c s3r x))(c s3 x )) )))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) ) (exists ((y T))  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s3 x) (c s1 x) ) (and (c s2 y) (not (c s2r y)) (not (c s3 y)) (not (c s1 y)) (= (elem y) a) (= (parent y) x) (= (ts y) i)  ) ) )))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (or (c s3r x)(not (c s3 x)) (not (c s1 x)) )) (= s1 s2) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s2 y)) (or (c s1 y) (and (= (elem y) a) (= (parent y) x) (= (ts y) i) (c s3 x) (not (c s3r x)) (c s1 x) (not (c s3 y)))  ) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=>  (add s3 s3r s1 s1r x a i s2 s2r) (= s1r s2r) )))

(declare-fun remove(S S S S T S S) Bool)
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (remove s3 s3r s1 s1r x s2 s2r) (= s1 s2) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s3 x)) (c s2r x) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s1r y)) (c s2r y) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s2r y)) (or (c s1r y) (and (= x y) (c s3 y)) ) ) ))

(declare-fun cl (S S T) Bool)
(assert (forall ((s S) (sr S) (t T)) (= (cl s sr t) (and (c s t) (not (c sr t)) ) )  ))

(declare-fun apply (E S S S S) Bool)
(assert (forall ((e E) (s1 S) (s1r S) (s2 S) (s2r S)) (= (apply e s1 s1r s2 s2r)
  (ite (= (op e) Add) (add (src e) (srcr e) s1 s1r (argE e) (argN e) (eid e) s2 s2r ) (remove (src e) (srcr e) s1 s1r (argE e) s2 s2r ) ) ) ))

;Encoding NON-INTERF-2 begins
;Encoding the antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(declare-const ss1r S)
(declare-const ss2r S)
(assert (not (= e1 e2)))

(declare-fun vis1 (E E) Bool)
(assert  (ite (vis1 e2 e1) (apply e2 ss1 ss1r  (src e1) (srcr e1)) (and (= (src e1) ss1) (= (srcr e1) ss1r) ) ))
(assert  (ite (vis1 e1 e2) (apply e1 ss2 ss2r  (src e2) (srcr e2)) (and (= (src e2) ss2) (= (srcr e2) ss2r) ) ))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)


(declare-const s11 S)
(declare-const s12 S)
(declare-const s11r S)
(declare-const s12r S)

(assert (apply e1 s0 s0r s11 s11r))
(assert (apply e2 s11 s11r s12 s12r))
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)
(declare-const s21r S)
(declare-const s22r S)


(assert (apply e2 s0 s0r s21 s21r))
(assert (apply e1 s21 s21r s22 s22r))
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))

(assert (forall ((t T)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2)))   (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (and (= (c s12 t) (c s22 t) ) (= (c s12r t) (c s22r t) )) )))


;Encoding the consequent
(declare-const e3 E)
(declare-const ss3 S)
(declare-const ss3r S)

(declare-const e1p E)
(declare-const e2p E)
(assert (= (argE e1) (argE e1p)))
(assert (= (argE e2) (argE e2p)))
(assert (= (argN e1) (argN e1p)))
(assert (= (argN e2) (argN e2p)))
 (assert (= (eid e1) (eid e1p)))
 (assert (= (eid e2) (eid e2p)))
 (assert (= (op e1) (op e1p)))
 (assert (= (op e2) (op e2p)))
(assert (not (= e1p e3)))
(assert (not (= e2p e3)))

(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))
(assert (= (srcr e3) ss3r))

(assert (= (vis1 e1 e2) (vis e1p e2p) ))
(assert (= (vis1 e2 e1) (vis e2p e1p) ))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (and (= (src e1p) ss1) (= (srcr e1p) ss1r) ) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (and (= (src e2p) ss2) (= (srcr e2p) ss2r) ) ))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (apply e3 ss1 ss1r  (src e1p) (srcr e1p) )   ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (apply e2p ss1 ss1r  (src e1p) (srcr e1p))  ) )
(assert (exists ((ns S) (nsr S))(=> (and (vis e3 e1p) (vis e2p e1p)) (and (apply e3 ss1 ss1r ns nsr) (apply e2p ns nsr (src e1p) (srcr e1p)) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (apply e3 ss2 ss2r (src e2p) (srcr e2p))    ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p))  (apply e1p ss2 ss2r  (src e2p)(srcr e2p))    ) )
(assert (exists ((ns S)(nsr S))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (apply e3 ss2 ss2r ns nsr)  (apply e1p ns nsr (src e2p) (srcr e2p))  )  ) ))

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
;
 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))
;

(assert (apply pe11 s0 s0r se11 se11r) )
(assert (apply pe12 se11 se11r  se12 se12r) )
(assert (eoe1 pe11 pe12))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe1 e1 e2) (eoe1 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe1 e1 e2)) ))

(declare-const pe21 E)
(declare-const pe22 E)
(declare-fun next2 (E E) Bool)
(declare-fun eoe2 (E E) Bool)
;
 (assert (or (= pe21 e1p) (= pe21 e2p)))
 (assert (or (= pe22 e1p) (= pe22 e2p)))
 (assert (not (= pe21 pe22)))


(assert (apply pe21 s0 s0r se21 se21r))
(assert  (apply pe22 se21 se21r se22 se22r) )
(assert (eoe2 pe21 pe22))

 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (cl se12 se12r a) (cl se22 se22r a))))

;Consistency Policy-PSI
;Note that two add operations involve the same list element if the either of argument of the operations or the element inserted by the ;operations are the same
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2))) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2))) (vis e1 e2)) (eo e1 e2) ) ))

(check-sat)
(get-model)
