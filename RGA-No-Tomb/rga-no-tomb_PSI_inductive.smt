;Encoding NON-INTERF-2

;Datatype declarations
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
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-const s0 S)

(declare-fun tso (I I) Bool)
(assert (forall ((t1 I) (t2 I) (t3 I)) (=> (and (tso t1 t2) (tso t2 t3)) (tso t1 t3) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (not (= t1 t2)) (or (tso t1 t2) (tso t2 t1)) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (tso t1 t2) (not (tso t2 t1)) ) ))

(assert (forall ( (t1 T) (t2 T)) (=>  (= (ts t1) (ts t2))  (= t1 t2) ) ))

;Encoding RGA-NO-TOMB CRDT
(declare-fun c (S T) Bool)
(declare-fun add (S S T A I S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s1 y)) (c s2 y) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s3 y)) (tso (ts y) i) ) ))
(assert (forall ((x T) (a A) (s1 S)  (s2 S) (s3 S) (i I) (y T) )  (=>  (add s3 s1 x a i s2) (c s3 x ) )))
(assert (forall ((x T) (a A) (s1 S)  (s2 S) (s3 S) (i I) ) (exists ((y T))  (=> (and (add s3 s1 x a i s2) (c s3 x) (c s1 x) ) (and (c s2 y) (not (c s3 y)) (not (c s1 y)) (= (elem y) a) (= (parent y) x) (= (ts y) i)  ) ) )))
(assert (forall ((x T) (a A) (s1 S)  (s2 S) (s3 S) (i I) )  (=> (and (add s3 s1 x a i s2) (or (not (c s3 x)) (not (c s1 x)) )) (= s1 s2) ) ))
(assert (forall ((x T) (a A) (s1 S)  (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s2 y)) (or (c s1 y) (and (= (elem y) a) (= (parent y) x) (= (ts y) i) (c s3 x)  (c s1 x) (not (c s3 y)))  ) ) ))

(declare-fun remove(S S T S) Bool)
(assert (forall ((x T)  (s1 S) (s2 S) (s3 S) (y T) ) (=> (remove s3 s1 x s2) (= (c s2 y) (ite (and (c s3 x) (= x y)) false (c s1 y) )) ) ))


;Encoding NON-INTERF-2 begins
;Encoding the antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(assert (not (= e1 e2)))


(declare-fun vis1 (E E) Bool)
(assert  (ite (vis1 e1 e2) (ite (= (op e1) Add) (add (src e1) ss2 (argE e1) (argN e1) (eid e1) (src e2)) (remove (src e1) ss2 (argE e1) (src e2)) ) (= (src e2) ss2) ))
(assert  (ite (vis1 e2 e1) (ite (= (op e2) Add) (add (src e2) ss1 (argE e2) (argN e2) (eid e2) (src e1)) (remove (src e2) ss1 (argE e2) (src e1)) ) (= (src e1) ss1) ))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)


(declare-const s11 S)
(declare-const s12 S)

(assert (ite (= (op e1) Add) (add (src e1) s0 (argE e1) (argN e1) (eid e1) s11) (remove (src e1) s0 (argE e1) s11) ))
(assert (ite (= (op e2) Add) (add (src e2) s11 (argE e2) (argN e2) (eid e2) s12) (remove (src e2) s11 (argE e2) s12)  ))
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)

(assert  (ite (= (op e2) Add) (add (src e2) s0 (argE e2) (argN e2) (eid e2) s21) (remove (src e2) s0 (argE e2) s21) ))
(assert (ite (= (op e1) Add) (add (src e1) s21 (argE e1) (argN e1) (eid e1) s22) (remove (src e1) s21 (argE e1) s22)))
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))

(assert (forall ((t T)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2)))   (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) ) (= (c s12 t) (c s22 t)) )))


;Encoding the consequent
(declare-const e3 E)
(declare-const ss3 S)
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

(assert (not (= (eid e1p) (eid e3))))
(assert (not (= (eid e2p) (eid e3))))
(assert (not (= (eid e1p) (eid e2p))))

(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))


(assert (= (vis1 e1 e2) (vis e1p e2p) ))
(assert (= (vis1 e2 e1) (vis e2p e1p) ))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (= (src e1p) ss1) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (= (src e2p) ss2) ))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (ite (= (op e3) Add) (add (src e3) ss1 (argE e3) (argN e3) (eid e3)  (src e1p))
  (remove (src e3) ss1 (argE e3) (src e1p)) )  ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (ite (= (op e2p) Add) (add (src e2p) ss1 (argE e2p) (argN e2p) (eid e2p)  (src e1p))
  (remove (src e2p) ss1 (argE e2p) (src e1p)) )  ) )
(assert (exists ((ns S))(=> (and (vis e3 e1p) (vis e2p e1p)) (and (ite (= (op e3) Add) (add (src e3) ss1 (argE e3) (argN e3) (eid e3)  ns)
  (remove (src e3) ss1 (argE e3) ns)) (ite (= (op e2p) Add) (add (src e2p) ns (argE e2p) (argN e2p) (eid e2p)  (src e1p))
    (remove (src e2p) ns (argE e2p) (src e1p))) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (ite (= (op e3) Add) (add (src e3) ss2 (argE e3) (argN e3) (eid e3)  (src e2p))
  (remove (src e3) ss2 (argE e3) (src e2p)) )    ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p))  (ite (= (op e1p) Add) (add (src e1p) ss2 (argE e1p) (argN e1p) (eid e1p)  (src e2p))
  (remove (src e1p) ss2 (argE e1p) (src e2p)) )   ) )
(assert (exists ((ns S))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (ite (= (op e3) Add) (add (src e3) ss2 (argE e3) (argN e3) (eid e3) ns)
(remove (src e3) ss2 (argE e3) ns) )  (ite (= (op e1p) Add) (add (src e1p) ns (argE e1p) (argN e1p) (eid e1p) (src e2p))
  (remove (src e1p) ns (argE e1p) (src e2p)) )  )  ) ))

(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-fun next1 (E E) Bool)
;
 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))
;

(assert (ite (= (op pe11) Add) (add (src pe11) s0 (argE pe11) (argN pe11) (eid pe11)  se11) (remove (src pe11) s0 (argE pe11) se11)) )
(assert (ite (= (op pe12) Add) (add (src pe12) se11 (argE pe12) (argN pe12) (eid pe12)  se12) (remove (src pe12) se11 (argE pe12) se12) ))
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


(assert (ite (= (op pe21) Add) (add (src pe21) s0 (argE pe21) (argN pe21) (eid pe21) se21) (remove (src pe21) s0 (argE pe21) se21) ))
(assert  (ite (= (op pe22) Add) (add (src pe22) se21 (argE pe22) (argN pe22) (eid pe22) se22) (remove (src pe22) se21 (argE pe22) se22) ))
(assert (eoe2 pe21 pe22))

 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (c se12 a) (c se22 a))))


;Consistency Policy-PSI
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (argE e1) (argE e2)) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (argE e1) (argE e2))  (vis e1 e2)) (eo e1 e2) ) ))

(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2)))  ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2)))  (vis e1 e2)) (eo e1 e2) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e2) (ts (argE e1)))  (vis e1 e2)) (eo e1 e2) ) ))



(check-sat)
(get-model)
