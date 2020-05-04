;Encoding NON-INTERF-2

;Declaration of datatypes
;Coming from the CRDT
(declare-sort T) ;Tuple datatype for Vertex-ORSet
(declare-sort Te) ;Tuple datatype for Edge-ORSet
(declare-sort A) ;Element datatype for Vertex
(declare-sort Ae) ;Element datatype for Edge
(declare-sort S) ;Set datatype for Vertex
(declare-sort Se) ;Set datatype for Edge
(declare-datatypes () ((OpType (AV) (RV) (AE) (RE) )))

;Coming from the verification framework
(declare-sort E) ;Event
(declare-sort I) ;Event-ID

;Functions and Predicates
(declare-fun elem (T) A) ;Element projection for vertex ORset
(declare-fun eleme (Te) Ae) ;Element projection for edge ORSet
(declare-fun id (T) I) ;Identifier projection for vertex
(declare-fun ide (Te) I) ;Identifier projection for edge
(declare-fun op (E) OpType)
(declare-fun arg (E) A) ;Vertex argument
(declare-fun arge (E) Ae) ;Edge argument
(declare-fun src (E) S) ;Vertex ORset at source replica
(declare-fun srce (E) Se) ;Edge ORset at source replica
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-fun sV (Ae) A) ;Start vertex given an edge
(declare-fun eV (Ae) A) ;End vertex given an edge
(declare-const s0 S)
(declare-const s0e Se)

;Encoding for Graph using ORset

;Vertex ORSet encoding
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

(declare-fun ca (S A) Bool) ;Vertex ORSet contains predicate
(assert (forall ((s S) (a A) (x T) ) (=> (and (c s x) (= (elem x) a) ) (ca s a) ) ))
(assert (forall ((s S) (a A) ) (exists ((x T))  (=> (ca s a) (and (c s x) (= (elem x) a)) ) ) ))

;Edge ORSet encoding
(declare-fun ce (Se Te) Bool)
(assert (forall ( (t1 Te) (t2 Te)) (=>  (= (ide t1) (ide t2))  (= t1 t2) ) ))
(declare-fun adde (Se Se Ae I Se) Bool)
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) (i I) )  (=> (and (adde s3 s1 a i s2) (ce s1 x)) (ce s2 x) ) ))
(assert (forall ( (a Ae) (s1 Se) (s2 Se) (s3 Se) (i I) ) (exists ((x Te)) (=>  (adde s3 s1 a i s2 ) (and (not (= s1 s2)) (ce s2 x) (= (eleme x) a) (= (ide x) i) (not (ce s1 x)) (not (ce s3 x))) ) ) ))
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) (i I) ) (=> (and (adde s3 s1 a i s2) (ce s2 x)) (or (ce s1 x) (and (not (ce s1 x)) (= (eleme x) a) (= (ide x) i))) ) ) )


(declare-fun removee (Se Se Ae Se) Bool)
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) )  (=> (and (removee s3 s1 a s2 ) (ce s3 x) (= (eleme x) a) )(not (ce s2 x)) ) ))
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) )  (=> (and (removee s3 s1 a s2 ) (ce s1 x) (not (= (eleme x) a)) )  (ce s2 x) ) ))
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) )  (=> (and (removee s3 s1 a s2 ) (ce s1 x)  (= (eleme x) a) (not (ce s3 x))  ) (ce s2 x) ) ))
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) )  (=> (and (removee s3 s1 a s2 ) (ce s2 x)) (or (not (= (eleme x) a)) (and (= (eleme x) a)
  (not (ce s3 x)) ) ) ) ))
(assert (forall ((x Te) (a Ae) (s1 Se) (s2 Se) (s3 Se) )  (=> (and (removee s3 s1 a s2 ) (ce s2 x)) (ce s1 x) ) ))

(declare-fun cae (Se Ae) Bool) ;Edge ORSet contains predicate
(assert (forall ((s Se) (a Ae) (x Te) ) (=> (and (ce s x) (= (eleme x) a) ) (cae s a) ) ))
(assert (forall ((s Se) (a Ae) ) (exists ((x Te))  (=> (cae s a) (and (ce s x) (= (eleme x) a)) ) ) ))

;Encoding Graph operations
(declare-fun addV (S Se S Se A I S Se) Bool)
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a A) (s2 S) (s2e Se)) (=> (addV s3 s3e s1 s1e a i s2 s2e) (and (= s1e s2e)
  (add s3 s1 a i s2) ) ) ))

(declare-fun remV (S Se S Se A S Se) Bool)
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (a A) (s2 S) (s2e Se)) (exists ((e Ae)) (=> (and (remV s3 s3e s1 s1e a s2 s2e) (ca s3 a)
  (=> (cae s3e e) (and (not (= (sV e) a)) (not (= (eV e) a))  ) ) (=> (cae s1e e) (and (not (= (sV e) a)) (not (= (eV e) a))  ) )  )
    (remove s3 s1 a s2)  )  ) ))
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (a A) (s2 S) (s2e Se) (e Ae))  (=> (and (remV s3 s3e s1 s1e a s2 s2e) (or (cae s3e e)
  (cae s1e e)) (or (= (sV e) a) (= (eV e) a)) )  (= s1 s2)
      )  ) )
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (a A) (s2 S) (s2e Se) )  (=> (and (remV s3 s3e s1 s1e a s2 s2e) (not (ca s3 a)) )  (= s1 s2)
      )  ) )
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (a A) (s2 S) (s2e Se)) (=> (remV s3 s3e s1 s1e a s2 s2e) (= s1e s2e) )  ))

(declare-fun addE (S Se S Se Ae I S Se) Bool)
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a Ae) (s2 S) (s2e Se)) (=> (addE s3 s3e s1 s1e a i s2 s2e) (and (ca s3 (sV a))
  (ca s3 (eV a)))  )  ))
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a Ae) (s2 S) (s2e Se)) (=> (and (addE s3 s3e s1 s1e a i s2 s2e) (ca s3 (sV a))
  (ca s3 (eV a)) (ca s1 (sV a)) (ca s1 (eV a)) ) (adde s3e s1e a i s2e) )  ))
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a Ae) (s2 S) (s2e Se)) (=> (and (addE s3 s3e s1 s1e a i s2 s2e) (or (not (ca s3 (sV a))) (not (ca s3 (eV a))) (not (ca s1 (sV a)) ) (not (ca s1 (eV a))) ) ) (= s1e s2e)  )  ))
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a Ae) (s2 S) (s2e Se)) (=> (addE s3 s3e s1 s1e a i s2 s2e) (= s1 s2) ) ))

(declare-fun remE (S Se S Se Ae S Se) Bool)
(assert (forall ((s3 S) (s3e Se) (s1 S) (s1e Se) (i I)(a Ae) (s2 S) (s2e Se) ) (=> (remE s3 s3e s1 s1e a s2 s2e) (and (= s1 s2) (removee s3e s1e a s2e))  )))

;Encoding NON-INTERF-2 begins
;Encoding antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss2 S)
(declare-const ss1e Se)
(declare-const ss2e Se)
(assert (not (= e1 e2)))

;vis = empty

(declare-fun vis1 (E E) Bool)
(assert (= (src e1) ss1))
(assert (= (src e2) ss2))
(assert (= (srce e1) ss1e))
(assert (= (srce e2) ss2e))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)
(assert (forall ((x1 E) (x2 E)) (not (vis1 x1 x2)) ))

(declare-fun apply (E S Se S Se) Bool)
(assert (forall ( (s1 S) (s1e Se) (s2 S) (s2e Se)(e E)) (= (apply e s1 s1e s2 s2e) (
  ite (= (op e) AV) (addV (src e) (srce e) s1 s1e (arg e) (eid e) s2 s2e) (ite (= (op e) RV) (remV (src e) (srce e) s1 s1e (arg e) s2 s2e) (ite (= (op e) AE) (addE (src e) (srce e) s1 s1e (arge e) (eid e) s2 s2e) (remE (src e) (srce e) s1 s1e (arge e) s2 s2e) ) )
  ) ) ))

(declare-const s11 S)
(declare-const s12 S)

(declare-const s11e Se)
(declare-const s12e Se)

(assert (apply e1 s0 s0e s11 s11e) )
(assert (apply e2 s11 s11e s12 s12e ) )
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)

(declare-const s21e Se)
(declare-const s22e Se)

(assert (apply e2 s0 s0e s21 s21e) )
(assert (apply e1 s21 s21e s22 s22e ) )
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))

(assert (forall ((a T) (ae Te)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2))) (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (and (= (c s12 a) (c s22 a))
  (= (ce s12e ae) (ce s22e ae)) ) )))
;(assert (forall ((e1 E) (e2 E)) (=> (vis1 e1 e2) (not (vis1 e2 e1)) )))
;(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis1 x1 x2) (vis1 x2 x3)) (vis1 x1 x3) ) ))
;(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (or (vis e1 e2)(vis e2 e1)) )))
;(assert (forall ((e1 E) (e2 E)) (=> (vis1 e1 e2) (eo1 e1 e2) ) ))
;(assert (forall ((e1 E) (e2 E)) (=> (vis1 e1 e2) (eo2 e1 e2) ) ))

;(assert (forall ((t T)) (= (c s12 t) (c s22 t))))

;vis = e1,e2

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
; (assert (ite (= (op e1a) A) (add (src e1a) ss2 (arg e1a) (eid e1a) (src e2a)) (remove (src e1a) ss2 (arg e1a) (src e2a))  )   )
; (declare-fun eo3 (E E) Bool)
; (declare-fun eo4 (E E) Bool)
; (assert (vis2 e1a e2a))
; (assert (not (vis2 e2a e1a)))
;
; (declare-const p11 S)
; (declare-const p12 S)
;
; (assert (ite (= (op e1a) A) (add (src e1a) s0 (arg e1a) (eid e1a) p11) (remove (src e1a) s0 (arg e1a) p11) ))
; (assert (ite (= (op e2a) A) (add (src e2a) p11 (arg e2a) (eid e2a) p12) (remove (src e2a) p11 (arg e2a) p12) ))
; (assert (eo3 e1a e2a))
; (assert (not (eo3 e2a e1a)))
;
; (declare-const p21 S)
; (declare-const p22 S)
;
; (assert (ite (= (op e2a) A) (add (src e2a) s0 (arg e2a) (eid e2a) p21) (remove (src e2a) s0 (arg e2a) p21) ))
; (assert (ite (= (op e1a) A) (add (src e1a) p21 (arg e1a) (eid e1a) p22) (remove (src e1a) p21 (arg e1a) p22) ))
; (assert (eo4 e2a e1a))
; (assert (not (eo4 e1a e2a)))
;
; (assert (forall ((t T)) (=> (and (=> (vis2 e1a e2a) (not (vis2 e2a e1a)))  (=> (vis2 e2a e1a) (not (vis2 e1a e2a))) (=> (vis2 e1a e2a) (eo3 e1a e2a)) (=> (vis2 e2a e1a) (eo3 e2a e1a)) (=> (vis2 e1a e2a) (eo4 e1a e2a)) (=> (vis2 e2a e1) (eo4 e2 e1a)) (=> (eo3 e1a e2a) (not (eo3 e2a e1a))) (=> (eo3 e2a e1a) (not (eo3 e1a e2a))) (=> (eo4 e1a e2a) (not (eo4 e2a e1a))) (=> (eo4 e2a e1a) (not (eo4 e1a e2a))) ) (= (c p12 t) (c p22 t)) )))
;
;Encoding consequent
(declare-const e3 E)
(declare-const ss3 S)
(declare-const ss3e Se)
(declare-const e1p E)
(declare-const e2p E)
(assert (= (op e1) (op e1p)))
(assert (= (op e2) (op e2p)))
(assert (= (arg e1) (arg e1p)))
(assert (= (arg e2) (arg e2p)))
(assert (= (arge e1) (arge e1p)))
(assert (= (arge e2) (arge e2p)))
(assert (= (eid e1) (eid e1p)))
(assert (= (eid e2) (eid e2p)))
(assert (not (= e1p e3)))
(assert (not (= e2p e3)))

(assert (not (= (eid e1p) (eid e2p))))
(assert (not (= (eid e1p) (eid e3))))
(assert (not (= (eid e3) (eid e2p))))


(assert (forall ((t T)) (=> (c s0 t) (not (= (id t) (eid e1) ))) ))
(assert (forall ((t T)) (=> (c s0 t) (not (= (id t) (eid e2) ))) ))
(assert (forall ((t T)) (=> (c s0 t) (not (= (id t) (eid e3) ))) ))

(assert (forall ((t Te)) (=> (ce s0e t) (not (= (ide t) (eid e1) ))) ))
(assert (forall ((t Te)) (=> (ce s0e t) (not (= (ide t) (eid e2) ))) ))
(assert (forall ((t Te)) (=> (ce s0e t) (not (= (ide t) (eid e3) ))) ))


(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))
(assert (= (srce e3) ss3e))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (and (= (src e1p) ss1) (= (srce e1p) ss1e)) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (and (= (src e2p) ss2) (= (srce e2p) ss2e)) ))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (apply e3 ss1 ss1e (src e1p) (srce e1p)  )   ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (apply e2p ss1 ss1e (src e1p) (srce e1p))   ) )
(assert (exists ((ns S) (nse Se))(=> (and (vis e3 e1p) (vis e2p e1p)) (and (apply e3 ss1 ss1e ns nse ) (apply e2p ns nse (src e1p) (srce e1p) ) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (apply e3 ss2 ss2e (src e2p) (srce e2p))   ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p)) (apply e1p ss2 ss2e (src e2p) (srce e2p))   ) )
(assert (exists ((ns S) (nse Se))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (apply e3 ss2 ss2e ns nse ) (apply e1p ns nse (src e2p) (srce e2p)) )  ) ))

(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-const se11e Se)
(declare-const se12e Se)
(declare-const se21e Se)
(declare-const se22e Se)
(declare-fun next1 (E E) Bool)

(assert (or (= pe11 e1p) (= pe11 e2p)))
(assert (or (= pe12 e1p) (= pe12 e2p)))
(assert (not (= pe11 pe12)))




(assert (apply pe11 s0 s0e se11 se11e) )
(assert (apply pe12 se11 se11e se12 se12e))
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

(assert (apply pe21 s0 s0e se21 se21e))
(assert (apply pe22 se21 se21e se22 se22e))
(assert (eoe2 pe21 pe22))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const aval A)
(declare-const ae Ae)

(assert  (or (not (= (ca se12 aval) (ca se22 aval))) (not (= (cae se12e ae) (cae se22e ae)))  ))

;Consistency Policy
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis x1 x2) (vis x2 x3)) (vis x1 x3) ) ))
;(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (or (= (eV (arge e1)) (arg e2)) (= (sV (arge e1)) (arg e2))) (= (op e1) AE) (= (op e2) RV) ) (or (vis e1 e2) (vis e2 e1) ) )))
; (assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (or (= (eV (arge e2)) (arg e1)) (= (sV (arge e2)) (arg e1))) (= (op e2) AE) (= (op e1) RV) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (or (= (eV (arge e1)) (arg e2)) (= (sV (arge e1)) (arg e2))) (= (op e1) RE) (= (op e2) RV) ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (or (= (eV (arge e2)) (arg e1)) (= (sV (arge e2)) (arg e1))) (= (op e2) RE) (= (op e1) RV) ) (or (vis e1 e2) (vis e2 e1) ) )))
;(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (or (vis e1 e2)(vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (eo e1 e2) ) ))

;We encode the convergence of the ORSet CRDT by asserting that if any two of the three events (e1,e2,e3) perform ORSet operations on the same set (i.e. both operations are either on the vertex set or the edge set), then they commute with each other
(define-fun addsrcV ((e1 E) (e2 E)) S
  (ite (= (op e1) AV) (src e1) (ite (= (op e2) AV) (src e2) ss1 ))
  )

(define-fun addargV ((e1 E) (e2 E)) A
  (ite (= (op e1) AV) (arg e1) (ite (= (op e2) AV) (arg e2) (arg e1) ))
  )

(define-fun addid ((e1 E) (e2 E)) I
  (ite (or (= (op e1) AV) (= (op e1) AE) ) (eid e1) (ite (or (= (op e2) AV) (= (op e2) AE) ) (eid e2) (eid e1) ))
  )

(define-fun remsrcV ((e1 E) (e2 E)) S
  (ite (= (op e1) RV) (src e1) (ite (= (op e2) RV) (src e2) ss1 ))
  )

(define-fun remargV ((e1 E) (e2 E)) A
  (ite (= (op e1) RV) (arg e1) (ite (= (op e2) RV) (arg e2) (arg e1) ))
  )

(declare-const asv S)
(assert (= asv (addsrcV e1 e2)))

(declare-const aav A)
(assert (= aav (addargV e1 e2)))

(declare-const ai I)
(assert (= ai (addid e1 e2)))

(declare-const rsv S)
(assert (= rsv (remsrcV e1 e2)))

(declare-const rav A)
(assert (= rav (remargV e1 e2)))


(define-fun addsrcE ((e1 E) (e2 E)) Se
  (ite (= (op e1) AE) (srce e1) (ite (= (op e2) AE) (srce e2) ss1e ))
  )

(define-fun addargE ((e1 E) (e2 E)) Ae
  (ite (= (op e1) AE) (arge e1) (ite (= (op e2) AE) (arge e2) (arge e1) ))
  )

(define-fun remsrcE ((e1 E) (e2 E)) Se
  (ite (= (op e1) RE) (srce e1) (ite (= (op e2) RE) (srce e2) ss1e ))
  )

(define-fun remargE ((e1 E) (e2 E)) Ae
  (ite (= (op e1) RE) (arge e1) (ite (= (op e2) RE) (arge e2) (arge e1) ))
  )

(declare-const ase Se)
(assert (= ase (addsrcE e1 e2)))

(declare-const aae Ae)
(assert (= aae (addargE e1 e2)))

(declare-const rse Se)
(assert (= rse (remsrcE e1 e2)))

(declare-const rae Ae)
(assert (= rae (remargE e1 e2)))

(declare-const bothv Bool)
(assert (= bothv (or (and (= (op e1) AV) (= (op e2) RV) ) (and (= (op e2) AV) (= (op e1) RV) ) ) ))

(declare-const bothe Bool)
(assert (= bothe (or (and (= (op e1) AE) (= (op e2) RE) ) (and (= (op e2) AE) (= (op e1) RE) ) ) ))


(assert (forall ((t T) (as11 S) (as12 S) (as21 S) (as22 S) ) (=> (and bothv (add asv s0 aav ai as11) (remove rsv as11 rav as12) (remove rsv s0 rav as21) (add asv as21 aav ai as22)  ) (= (c as12 t) (c as22 t)) ) ))


(assert (forall ((t Te) (as11 Se) (as12 Se) (as21 Se) (as22 Se) ) (=> (and bothe (adde ase s0e aae ai as11) (removee rse as11 rae as12) (removee rse s0e rae as21) (adde ase as21 aae ai as22)  ) (= (ce as12 t) (ce as22 t)) ) ))


(declare-const asv1 S)
(assert (= asv1 (addsrcV e1 e3)))

(declare-const aav1 A)
(assert (= aav1 (addargV e1 e3)))

(declare-const ai1 I)
(assert (= ai1 (addid e1 e3)))

(declare-const rsv1 S)
(assert (= rsv1 (remsrcV e1 e3)))

(declare-const rav1 A)
(assert (= rav1 (remargV e1 e3)))

(declare-const ase1 Se)
(assert (= ase1 (addsrcE e1 e3)))

(declare-const aae1 Ae)
(assert (= aae1 (addargE e1 e3)))

(declare-const rse1 Se)
(assert (= rse1 (remsrcE e1 e3)))

(declare-const rae1 Ae)
(assert (= rae1 (remargE e1 e3)))

(declare-const bothv1 Bool)
(assert (= bothv1 (or (and (= (op e1) AV) (= (op e3) RV) ) (and (= (op e3) AV) (= (op e1) RV) ) ) ))

(declare-const bothe1 Bool)
(assert (= bothe1 (or (and (= (op e1) AE) (= (op e3) RE) ) (and (= (op e3) AE) (= (op e1) RE) ) ) ))


(assert (forall ((t T) (as11 S) (as12 S) (as21 S) (as22 S) ) (=> (and bothv1 (add asv1 s0 aav1 ai1 as11) (remove rsv1 as11 rav1 as12) (remove rsv1 s0 rav1 as21) (add asv1 as21 aav1 ai1 as22)  ) (= (c as12 t) (c as22 t)) ) ))


(assert (forall ((t Te) (as11 Se) (as12 Se) (as21 Se) (as22 Se) ) (=> (and bothe1 (adde ase1 s0e aae1 ai1 as11) (removee rse1 as11 rae1 as12) (removee rse1 s0e rae1 as21) (adde ase1 as21 aae1 ai1 as22)  ) (= (ce as12 t) (ce as22 t)) ) ))


(declare-const asv2 S)
(assert (= asv2 (addsrcV e2 e3)))

(declare-const aav2 A)
(assert (= aav2 (addargV e2 e3)))

(declare-const ai2 I)
(assert (= ai2 (addid e2 e3)))

(declare-const rsv2 S)
(assert (= rsv2 (remsrcV e2 e3)))

(declare-const rav2 A)
(assert (= rav2 (remargV e2 e3)))

(declare-const ase2 Se)
(assert (= ase2 (addsrcE e2 e3)))

(declare-const aae2 Ae)
(assert (= aae2 (addargE e2 e3)))

(declare-const rse2 Se)
(assert (= rse2 (remsrcE e2 e3)))

(declare-const rae2 Ae)
(assert (= rae2 (remargE e2 e3)))

(declare-const bothv2 Bool)
(assert (= bothv2 (or (and (= (op e2) AV) (= (op e3) RV) ) (and (= (op e3) AV) (= (op e2) RV) ) ) ))

(declare-const bothe2 Bool)
(assert (= bothe2 (or (and (= (op e2) AE) (= (op e3) RE) ) (and (= (op e3) AE) (= (op e2) RE) ) ) ))


(assert (forall ((t T) (as11 S) (as12 S) (as21 S) (as22 S) ) (=> (and bothv2 (add asv2 s0 aav2 ai2 as11) (remove rsv2 as11 rav2 as12) (remove rsv2 s0 rav2 as21) (add asv2 as21 aav2 ai2 as22)  ) (= (c as12 t) (c as22 t)) ) ))


(assert (forall ((t Te) (as11 Se) (as12 Se) (as21 Se) (as22 Se) ) (=> (and bothe2 (adde ase2 s0e aae2 ai2 as11) (removee rse2 as11 rae2 as12) (removee rse2 s0e rae2 as21) (adde ase2 as21 aae2 ai2 as22)  ) (= (ce as12 t) (ce as22 t)) ) ))


(check-sat)
(get-model)
