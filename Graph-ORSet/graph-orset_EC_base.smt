;Encoding NON-INTERF-1

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
(declare-sort I) ;Event-Id

;Functions and Predicates
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

;Encoding NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)
(declare-fun vis (E E) Bool)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (and (= (src e1p) s0) (= (srce e1p) s0e)  ) ))
(assert (=> (not (vis e1p e2p))  (and (= (src e2p) s0) (= (srce e2p) s0e) ) ))

(declare-fun apply (E S Se S Se) Bool)
(assert (forall ( (s1 S) (s1e Se) (s2 S) (s2e Se)(e E)) (= (apply e s1 s1e s2 s2e) (
  ite (= (op e) AV) (addV (src e) (srce e) s1 s1e (arg e) (eid e) s2 s2e) (ite (= (op e) RV) (remV (src e) (srce e) s1 s1e (arg e) s2 s2e) (ite (= (op e) AE) (addE (src e) (srce e) s1 s1e (arge e) (eid e) s2 s2e) (remE (src e) (srce e) s1 s1e (arge e) s2 s2e) ) )
  ) ) ))

(assert (=> (vis e2p e1p) (apply e2p s0 s0e (src e1p) (srce e1p)  )   ) )
(assert (=> (vis e1p e2p) (apply e1p s0 s0e (src e2p) (srce e2p)  )   ) )



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
;
 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))
;

(assert (apply pe11 s0 s0e  se11 se11e ))
(assert (apply pe12 se11 se11e  se12 se12e ) )
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
;
 (assert (or (= pe21 e1p) (= pe21 e2p)))
 (assert (or (= pe22 e1p) (= pe22 e2p)))
 (assert (not (= pe21 pe22)))


(assert (apply pe21 s0 s0e  se21 se21e ))
(assert (apply pe22 se21 se21e  se22 se22e ) )
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))

 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))


(declare-const aval A)
(declare-const ae Ae)

(assert  (or (not (= (ca se12 aval) (ca se22 aval))) (not (= (cae se12e ae) (cae se22e ae)))  ))

;Consistency Policy-EC
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))

;We encode the convergence of the ORSet CRDT by asserting that if any two of the three events (e1,e2,e3) perform ORSet operations on the same set (i.e. both operations are either on the vertex set or the edge set), then they commute with each other
(define-fun addsrcV ((e1 E) (e2 E)) S
  (ite (= (op e1) AV) (src e1) (ite (= (op e2) AV) (src e2) s0 ))
  )

(define-fun addargV ((e1 E) (e2 E)) A
  (ite (= (op e1) AV) (arg e1) (ite (= (op e2) AV) (arg e2) (arg e1) ))
  )

(define-fun addid ((e1 E) (e2 E)) I
  (ite (or (= (op e1) AV) (= (op e1) AE) ) (eid e1) (ite (or (= (op e2) AV) (= (op e2) AE) ) (eid e2) (eid e1) ))
  )

(define-fun remsrcV ((e1 E) (e2 E)) S
  (ite (= (op e1) RV) (src e1) (ite (= (op e2) RV) (src e2) s0 ))
  )

(define-fun remargV ((e1 E) (e2 E)) A
  (ite (= (op e1) RV) (arg e1) (ite (= (op e2) RV) (arg e2) (arg e1) ))
  )

(declare-const asv S)
(assert (= asv (addsrcV e1p e2p)))

(declare-const aav A)
(assert (= aav (addargV e1p e2p)))

(declare-const ai I)
(assert (= ai (addid e1p e2p)))

(declare-const rsv S)
(assert (= rsv (remsrcV e1p e2p)))

(declare-const rav A)
(assert (= rav (remargV e1p e2p)))


(define-fun addsrcE ((e1 E) (e2 E)) Se
  (ite (= (op e1) AE) (srce e1) (ite (= (op e2) AE) (srce e2) s0e ))
  )

(define-fun addargE ((e1 E) (e2 E)) Ae
  (ite (= (op e1) AE) (arge e1) (ite (= (op e2) AE) (arge e2) (arge e1) ))
  )

(define-fun remsrcE ((e1 E) (e2 E)) Se
  (ite (= (op e1) RE) (srce e1) (ite (= (op e2) RE) (srce e2) s0e ))
  )

(define-fun remargE ((e1 E) (e2 E)) Ae
  (ite (= (op e1) RE) (arge e1) (ite (= (op e2) RE) (arge e2) (arge e1) ))
  )

(declare-const ase Se)
(assert (= ase (addsrcE e1p e2p)))

(declare-const aae Ae)
(assert (= aae (addargE e1p e2p)))

(declare-const rse Se)
(assert (= rse (remsrcE e1p e2p)))

(declare-const rae Ae)
(assert (= rae (remargE e1p e2p)))

(declare-const bothv Bool)
(assert (= bothv (or (and (= (op e1p) AV) (= (op e2p) RV) ) (and (= (op e2p) AV) (= (op e1p) RV) ) ) ))

(declare-const bothe Bool)
(assert (= bothe (or (and (= (op e1p) AE) (= (op e2p) RE) ) (and (= (op e2p) AE) (= (op e1p) RE) ) ) ))


(assert (forall ((t T) (as11 S) (as12 S) (as21 S) (as22 S) ) (=> (and bothv (add asv s0 aav ai as11) (remove rsv as11 rav as12) (remove rsv s0 rav as21) (add asv as21 aav ai as22)  ) (= (c as12 t) (c as22 t)) ) ))


(assert (forall ((t Te) (as11 Se) (as12 Se) (as21 Se) (as22 Se) ) (=> (and bothe (adde ase s0e aae ai as11) (removee rse as11 rae as12) (removee rse s0e rae as21) (adde ase as21 aae ai as22)  ) (= (ce as12 t) (ce as22 t)) ) ))



(check-sat)
(get-model)
