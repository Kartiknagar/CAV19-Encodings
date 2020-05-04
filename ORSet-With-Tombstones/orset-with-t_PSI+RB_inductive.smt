;Encoding NON-INTERF-2

;Datatype declaration
(declare-sort T)
(declare-sort A)
(declare-sort I)
(declare-sort S)
(declare-sort E)
(declare-datatypes () ((OpType (A) (R) )))
(declare-fun elem (T) A)
(declare-fun id (T) I)
(declare-fun op (E) OpType)
(declare-fun arg (E) A)
(declare-fun src (E) S)
(declare-fun srcr (E) S)
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-const s0 S)
(declare-const s0r S)

;Encoding of ORSet-with-tombstone
(declare-fun c (S T) Bool)
(assert (forall ( (t1 T) (t2 T)) (=>  (= (id t1) (id t2))  (= t1 t2) ) ))
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

;Encoding of NON-INTERF-2 begins
;Encoding the antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(declare-const ss1r S)
(declare-const ss2r S)
(assert (not (= e1 e2)))

(declare-fun vis1 (E E) Bool)
(assert  (ite (vis1 e1 e2) (ite (= (op e1) A) (add (src e1) (srcr e1) ss2 ss2r (arg e1) (eid e1) (src e2) (srcr e2)) (remove (src e1) (srcr e1) ss2 ss2r (arg e1) (src e2) (srcr e2) ) ) (and (= (src e2) ss2) (= (srcr e2) ss2r)) ))
(assert  (ite (vis1 e2 e1) (ite (= (op e2) A) (add (src e2) (srcr e2) ss1 ss1r (arg e2) (eid e2) (src e1) (srcr e1)) (remove (src e2) (srcr e2) ss1 ss1r (arg e2) (src e1) (srcr e1)) ) (and (= (src e1) ss1) (= (srcr e1) ss1r)) ))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)


(declare-const s11 S)
(declare-const s12 S)
(declare-const s11r S)
(declare-const s12r S)

(assert (ite (= (op e1) A) (add (src e1) (srcr e1) s0 s0r (arg e1) (eid e1) s11 s11r) (remove (src e1) (srcr e1) s0 s0r (arg e1) s11 s11r) ))
(assert (ite (= (op e2) A) (add (src e2) (srcr e2) s11 s11r (arg e2) (eid e2) s12 s12r) (remove (src e2) (srcr e2) s11 s11r (arg e2) s12 s12r) ))
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)
(declare-const s21r S)
(declare-const s22r S)

(assert (ite (= (op e2) A) (add (src e2) (srcr e2) s0 s0r (arg e2) (eid e2) s21 s21r) (remove (src e2) (srcr e2) s0 s0r (arg e2) s21 s21r) ))
(assert (ite (= (op e1) A) (add (src e1) (srcr e1) s21 s21r (arg e1) (eid e1) s22 s22r) (remove (src e1) (srcr e1) s21 s21r (arg e1) s22 s22r) ))
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))


(assert (forall ((t A)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2))) (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (= (ca s12 s12r t) (ca s22 s22r t)) )))



;Encoding of consequent
(declare-const e3 E)
(declare-const ss3 S)
(declare-const ss3r S)
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


(assert (not (= (eid e1p) (eid e2p))))
(assert (not (= (eid e1p) (eid e3))))
(assert (not (= (eid e3) (eid e2p))))

(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))
(assert (= (srcr e3) ss3r))


(assert (= (vis1 e1 e2) (vis e1p e2p) ))
(assert (= (vis1 e2 e1) (vis e2p e1p) ))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (= (src e1p) ss1) (= (srcr e1p) ss1r) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (= (src e2p) ss2) (= (srcr e2p) ss2r)))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (ite (= (op e3) A) (add (src e3) (srcr e3) ss1 ss1r (arg e3) (eid e3) (src e1p) (srcr e1p) ) (remove (src e3) (srcr e3) ss1 ss1r (arg e3) (src e1p) (srcr e1p) )  )   ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (ite (= (op e2p) A) (add (src e2p) (srcr e2p) ss1 ss1r (arg e2p) (eid e2p) (src e1p) (srcr e1p)) (remove (src e2p) (srcr e2p) ss1 ss1r (arg e2p) (src e1p)(srcr e1p) )  )   ) )
(assert (exists ((ns S) (nsr S) )(=> (and (vis e3 e1p) (vis e2p e1p)) (and (ite (= (op e3) A) (add (src e3) (srcr e3) ss1 ss1r (arg e3) (eid e3) ns nsr) (remove (src e3) (srcr e3) ss1 ss1r (arg e3) ns nsr)  ) (ite (= (op e2p) A) (add (src e2p) (srcr e2p) ns nsr (arg e2p) (eid e2p) (src e1p) (srcr e1p)) (remove (src e2p) (srcr e2p) ns nsr (arg e2p) (src e1p) (srcr e1p))  ) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (ite (= (op e3) A) (add (src e3) (srcr e3) ss2 ss2r (arg e3) (eid e3) (src e2p) (srcr e2p)) (remove (src e3) (srcr e3) ss2 ss2r (arg e3) (src e2p) (srcr e2p))  )   ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p)) (ite (= (op e1p) A) (add (src e1p) (srcr e1p) ss2 ss2r (arg e1p) (eid e1p) (src e2p) (srcr e2p)) (remove (src e1p) (srcr e1p) ss2 ss2r (arg e1p) (src e2p) (srcr e2p))  )   ) )
(assert (exists ((ns S) (nsr S))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (ite (= (op e3) A) (add (src e3) (srcr e3) ss2 ss2r (arg e3) (eid e3) ns nsr) (remove (src e3) (srcr e3) ss2 ss2r (arg e3) ns nsr)  ) (ite (= (op e1p) A) (add (src e1p) (srcr e1p) ns nsr (arg e1p) (eid e1p) (src e2p) (srcr e2p)) (remove (src e1p) (srcr e1p) ns nsr (arg e1p) (src e2p) (srcr e2p))  ) )  ) ))

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


(assert (ite (= (op pe11) A) (add (src pe11) (srcr pe11) s0 s0r (arg pe11) (eid pe11) se11 se11r) (remove (src pe11) (srcr pe11) s0 s0r (arg pe11) se11 se11r) ))
(assert (ite (= (op pe12) A) (add (src pe12) (srcr pe12) se11 se11r (arg pe12) (eid pe12) se12 se12r) (remove (src pe12) (srcr pe12) se11 se11r (arg pe12) se12 se12r) ))
(assert (eoe1 pe11 pe12))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe1 e1 e2) (eoe1 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe1 e1 e2)) ))

(declare-const pe21 E)
(declare-const pe22 E)
(declare-fun next2 (E E) Bool)
(declare-fun eoe2 (E E) Bool)

(assert (or (= pe21 e1p) (= pe21 e2p)))
(assert (or (= pe22 e1p) (= pe22 e2p)))
(assert (not (= pe21 pe22)))


(assert (ite (= (op pe21) A) (add (src pe21) (srcr pe21) s0 s0r (arg pe21) (eid pe21) se21 se21r) (remove (src pe21) (srcr pe21) s0 s0r (arg pe21) se21 se21r) ))
(assert (ite (= (op pe22) A) (add (src pe22) (srcr pe22) se21 se21r (arg pe22) (eid pe22) se22 se22r) (remove (src pe22) (srcr pe22) se21 se21r (arg pe22) se22 se22r) ))
(assert (eoe2 pe21 pe22))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a A)
(assert  (not (= (ca se12 se12r a) (ca se22 se22r a))))

;Consistency Policy-PSI+RB
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) (= (op e1) A) (= (op e2) R) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2)) (= (op e1) A) (= (op e2) R) (vis e1 e2)) (eo e1 e2) ) ))


(check-sat)
(get-model)
