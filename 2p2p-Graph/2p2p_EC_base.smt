;Encoding NON-INTERF-1

;Coming from the CRDT
(declare-sort A) ;Vertex Datatype
(declare-sort Ae) ;Edge Datatype
(declare-sort S) ;Set of Vertices
(declare-sort Se) ;Set of Edges
(declare-datatypes () ((OpType (AV) (RV) (AE) (RE) )))

;Coming from the verification framework
(declare-sort E) ;Event
(declare-sort I) ;Event-Id

;Functions and Predicates
(declare-fun op (E) OpType)
(declare-fun arg (E) A) ;Vertex Argument
(declare-fun arge (E) Ae) ;Edge Argument
(declare-fun src (E) S) ;Vertex Set at source replica
(declare-fun srct (E) S) ;Edge Set at source replica
(declare-fun srce (E) Se) ;Vertex tombstone at source replica
(declare-fun srcet (E) Se) ;Edge tombstone at source replica

(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-fun sV (Ae) A) ;Start Vertex given an edge
(declare-fun eV (Ae) A) ;End vertex given an edge
(declare-const s0 S)
(declare-const s0e Se)
(declare-const s0t S)
(declare-const s0et Se)



(declare-fun c (S A) Bool) ;contains predicate for vertex set
(declare-fun ce (Se Ae) Bool) ;contains predicate for edge set

;Encoding that edges incident on the same pair of vertices are equal
(assert (forall ((e1 Ae)(e2 Ae)) (=> (and (= (sV e1) (sV e2)) (= (eV e1) (eV e2)) ) (= e1 e2) ) ))

;Encoding empty initial states
(assert (forall ((a A)) (not (c s0 a)) ))
(assert (forall ((a A)) (not (c s0t a)) ))
(assert (forall ((a Ae)) (not (ce s0e a)) ))
(assert (forall ((a Ae)) (not (ce s0et a)) ))

;Encoding 2p2p graph CRDT
(declare-fun addV (S S Se Se S S Se Se A S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) )
  (=> (addV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (and (= s1t s2t) (= s1e s2e) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (x A) )
  (=> (addV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (= (c s2 x) (ite (= x a) true (c s1 x) )  )  )  ))

(declare-fun addE (S S Se Se S S Se Se Ae S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (and (= s1t s2t) (= s1 s2) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) (xe Ae) )
  (=> (and (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (c s3 (sV ae)) (c s3 (eV ae)) (not (c s3t (sV ae))) (not (c s3t (eV ae)))  )  (= (ce s2e xe) (ite (= xe ae) true (ce s1e xe) )  )    )))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (and (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (or (not (c s3 (sV ae))) (not (c s3 (eV ae)))  (c s3t (sV ae))  (c s3t (eV ae))  ))  (= s1e s2e  )    )))

(declare-fun removeV (S S Se Se S S Se Se A S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) )
  (=> (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (and (= s1 s2) (= s1e s2e) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (x A) ) (exists ((ae Ae))
   (=> (and (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (=> (and (ce s3e ae) (not (ce s3et ae))) (and (not (= (sV ae) a)) (not (= (eV ae) a)) )) (c s1 a) (c s3 a) (not (c s3t a)) ) (= (c s2t x) (ite (= x a) true (c s1t x) )  )  )  )))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (ae Ae) )
  (=> (and (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (or (not (c s3 a)) (c s3t a) (not (c s1 a)) (and (ce s3e ae)
    (not (ce s3et ae)) (or (= (sV ae) a) (= (eV ae) a) ) ) ) ) (= s1t s2t )  )  ))

(declare-fun removeE (S S Se Se S S Se Se Ae S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (and (= s1t s2t) (= s1 s2) (= s1e s2e)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (xe Ae) (ae Ae) )
  (=> (and (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (ce s3e ae) (not (ce s3et ae)) (ce s1e ae) ) (= (ce s2et xe) (ite (= xe ae) true (ce s1et xe) )  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (and (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (or (not (ce s3e ae)) (ce s3et ae) (not (ce s1e ae)) )  ) (= s1et s2et )  )  ))

(declare-fun lookupV (S S Se Se A) Bool)
(assert (forall ((s S) (st S) (se Se) (set Se) (a A) ) (= (lookupV s st se set a) (and (c s a) (not (c st a)) ) ) ))

(declare-fun lookupE (S S Se Se Ae) Bool)
(assert (forall ((s S) (st S) (se Se) (set Se) (ae Ae) ) (= (lookupE s st se set ae) (and (ce se ae) (not (ce set ae))
  (lookupV s st se set (sV ae)) (lookupV s st se set (eV ae)) ) ) ))


;Encoding NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)
(declare-fun vis (E E) Bool)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (and (= (src e1p) s0) (= (srct e1p) s0t) (= (srce e1p) s0e) (= (srcet e1p) s0et)) ))
(assert (=> (not (vis e1p e2p))  (and (= (src e2p) s0) (= (srct e2p) s0t) (= (srce e2p) s0e) (= (srcet e2p) s0et)) ))

(declare-fun apply (E S S Se Se S S Se Se) Bool)
(assert (forall ( (s1 S) (s1e Se) (s1t S) (s1et Se)  (s2 S) (s2e Se) (s2t S) (s2et Se) (e E)) (= (apply e s1 s1t s1e s1et s2 s2t s2e s2et) (
  ite (= (op e) AV) (addV (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arg e) s2 s2t s2e s2et) (ite (= (op e) RV) (removeV (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arg e) s2 s2t s2e s2et) (ite (= (op e) AE) (addE (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arge e) s2 s2t s2e s2et) (removeE (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arge e) s2 s2t s2e s2et) ) )
  ) ) ))

(assert (=> (vis e2p e1p) (apply e2p s0 s0t s0e s0et (src e1p) (srct e1p) (srce e1p) (srcet e1p) )   ) )
(assert (=> (vis e1p e2p) (apply e1p s0 s0t s0e s0et (src e2p) (srct e2p) (srce e2p) (srcet e2p) )   ) )



(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-const se11t S)
(declare-const se12t S)
(declare-const se21t S)
(declare-const se22t S)
(declare-const se11e Se)
(declare-const se12e Se)
(declare-const se21e Se)
(declare-const se22e Se)
(declare-const se11et Se)
(declare-const se12et Se)
(declare-const se21et Se)
(declare-const se22et Se)
(declare-fun next1 (E E) Bool)
;
 (assert (or (= pe11 e1p) (= pe11 e2p)))
 (assert (or (= pe12 e1p) (= pe12 e2p)))
 (assert (not (= pe11 pe12)))
;

(assert (apply pe11 s0 s0t s0e s0et se11 se11t se11e se11et))
(assert (apply pe12 se11 se11t se11e se11et se12 se12t se12e se12et) )
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


(assert (apply pe21 s0 s0t s0e s0et se21 se21t se21e se21et))
(assert (apply pe22 se21 se21t se21e se21et se22 se22t se22e se22et) )
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))

 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const aval A)
(declare-const ae Ae)

(declare-const vbool Bool)
(declare-const ebool Bool)

(assert (= vbool (not (= (lookupV se12 se12t se12e se12et aval) (lookupV se22 se22t se22e se22et aval))) ))
(assert (= ebool (not (= (lookupE se12 se12t se12e se12et ae) (lookupE se22 se22t se22e se22et ae))) ))

(assert (or vbool ebool))

;Consistency Policy-EC
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))

(check-sat)
(get-model)
