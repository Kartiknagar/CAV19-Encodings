;Encoding NON-INTERF-2

;Declaration of sorts
;Coming from the CRDT
(declare-sort T) ;Element Sort
(declare-sort S) ;Set Sort
(declare-datatypes () ((OpType (A) (R) )))

;Coming from the verification framework
(declare-sort E) ;Event Sort
(declare-sort I) ;Identifier Sort

(declare-fun op (E) OpType)
(declare-fun arg (E) T)
(declare-fun src (E) S)
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-const s0 S)

;Encoding of USet CRDT
(declare-fun c (S T) Bool) ;Contains predicate
(declare-fun add (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (add s3 s1 a s2) (= (c s2 x) (ite (and (= x a) (not (c s3 a)) ) true (c s1 x) ) ) ) ))

(declare-fun remove (S S T S) Bool)
(assert (forall ((x T) (a T) (s1 S) (s2 S) (s3 S) )  (=> (remove s3 s1 a s2) (= (c s2 x) (ite (and (= x a) (c s3 a) (c s1 a) ) false (c s1 x) ) ) ) ))

;Encoding NON-INTERF-1 begins
;Encoding Antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(assert (not (= e1 e2)))

;vis = empty

(declare-fun vis1 (E E) Bool)
(assert (= (src e1) ss1))
(assert (= (src e2) ss2))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)
(assert (forall ((x1 E) (x2 E)) (not (vis1 x1 x2)) ))


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

(assert (forall ((t T)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2)))  (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (= (c s12 t) (c s22 t)) )))

;vis = e1,e2
;
; (declare-const e1a E)
; (declare-const e2a E)
; (assert (= (op e1) (op e1a)))
; (assert (= (op e2) (op e2a)))
; (assert (= (arg e1) (arg e1a)))
; (assert (= (arg e2) (arg e2a)))
; (assert (= (eid e1) (eid e1a)))
; (assert (= (eid e2) (eid e2a)))
; (declare-fun vis2 (E E) Bool)
; (assert (= (src e1a) ss1))
; (assert (ite (= (op e1a) A) (add (src e1a) ss2 (arg e1a) (src e2a)) (remove (src e1a) ss2 (arg e1a) (src e2a))  )   )
; (declare-fun eo3 (E E) Bool)
; (declare-fun eo4 (E E) Bool)
; (assert (vis2 e1a e2a))
; (assert (not (vis2 e2a e1a)))
;
; (declare-const p11 S)
; (declare-const p12 S)
;
; (assert (ite (= (op e1a) A) (add (src e1a) s0 (arg e1a)  p11) (remove (src e1a) s0 (arg e1a) p11) ))
; (assert (ite (= (op e2a) A) (add (src e2a) p11 (arg e2a)  p12) (remove (src e2a) p11 (arg e2a) p12) ))
; (assert (eo3 e1a e2a))
; (assert (not (eo3 e2a e1a)))
;
; (declare-const p21 S)
; (declare-const p22 S)
;
; (assert (ite (= (op e2a) A) (add (src e2a) s0 (arg e2a)  p21) (remove (src e2a) s0 (arg e2a) p21) ))
; (assert (ite (= (op e1a) A) (add (src e1a) p21 (arg e1a)  p22) (remove (src e1a) p21 (arg e1a) p22) ))
; (assert (eo4 e2a e1a))
; (assert (not (eo4 e1a e2a)))
;
; ;(=> (= (arg e1a) (arg e2a)) (or (vis2 e1a e2a) (vis2 e2a e1a)) )
; (assert (forall ((t T)) (=> (and (=> (vis2 e1a e2a) (not (vis2 e2a e1a)))  (=> (vis2 e2a e1a) (not (vis2 e1a e2a)))  (=> (vis2 e1a e2a) (eo3 e1a e2a)) (=> (vis2 e2a e1a) (eo3 e2a e1a)) (=> (vis2 e1a e2a) (eo4 e1a e2a)) (=> (vis2 e2a e1) (eo4 e2 e1a)) (=> (eo3 e1a e2a) (not (eo3 e2a e1a))) (=> (eo3 e2a e1a) (not (eo3 e1a e2a))) (=> (eo4 e1a e2a) (not (eo4 e2a e1a))) (=> (eo4 e2a e1a) (not (eo4 e1a e2a))) ) (= (c p12 t) (c p22 t)) )))

;Encoding Consequent
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

(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))
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
;
 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))
;

(assert (ite (= (op pe11) A) (add (src pe11) s0 (arg pe11)  se11) (remove (src pe11) s0 (arg pe11) se11) ))
(assert (ite (= (op pe12) A) (add (src pe12) se11 (arg pe12)  se12) (remove (src pe12) se11 (arg pe12) se12) ))
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


(assert (ite (= (op pe21) A) (add (src pe21) s0 (arg pe21)  se21) (remove (src pe21) s0 (arg pe21) se21) ))
(assert (ite (= (op pe22) A) (add (src pe22) se21 (arg pe22)  se22) (remove (src pe22) se21 (arg pe22) se22) ))
(assert (eoe2 pe21 pe22))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (c se12 a) (c se22 a))))

;Consistency Policy-CC
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis x1 x2) (vis x2 x3)) (vis x1 x3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (eo e1 e2) ) ))

(check-sat)
(get-model)
