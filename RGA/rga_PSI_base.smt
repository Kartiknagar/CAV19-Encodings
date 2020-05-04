;Encoding NON-INTERF-1

;Coming from the CRDT
(declare-sort T) ;Tuple
(declare-sort S) ;Set
(declare-sort A) ;Element
(declare-datatypes () ((OpType (Add) (R) )))

;Coming from the verification framework
(declare-sort E) ;Event
(declare-sort I) ;Event-id

;Functions and Predicates
(declare-fun op (E) OpType)
(declare-fun elem (T) A) ;Element projection function
(declare-fun parent (T) T) ;Parent of the list element
(declare-fun ts (T) I) ;time-stamp projection function (event-id acts as the timestamp)
(declare-fun argE (E) T) ;The existing element of the list to the right of which the new element has to be added
(declare-fun argN (E) A) ;New element to be added
(declare-fun src (E) S) ;List at the source replica
(declare-fun srcr (E) S) ;Tombstone set at the source replica
(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-const s0 S)
(declare-const s0r S)
(declare-const start T) ;Leftmost element of the list, assumed to be present at the beginning
(declare-fun c (S T) Bool)

;Encoding that the start element is present in the initial state and no other element is present
(assert (c s0 start))
(assert (not (c s0r start)))
(assert (forall ((t T)) (=> (not (= t start)) (not (c s0 t)) ) ))

;Encoding the total order on the timestamps (identifiers) of list elements
(declare-fun tso (I I) Bool) ;Time stamp ordering
(assert (forall ((t1 I) (t2 I) (t3 I)) (=> (and (tso t1 t2) (tso t2 t3)) (tso t1 t3) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (not (= t1 t2)) (or (tso t1 t2) (tso t2 t1)) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (tso t1 t2) (not (tso t2 t1)) ) ))

;Encoding that the start element has the lowest timestamp, and elements have distinct timestamps
(assert (forall ((t T)) (=> (not (= t start)) (tso (ts start) (ts t) ) ) ))
(assert (forall ( (t1 T) (t2 T)) (=>  (= (ts t1) (ts t2))  (= t1 t2) ) ))


;Encoding the RGA CRDT
(declare-fun add (S S S S T A I S S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s1 y)) (c s2 y) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s3 y)) (tso (ts y) i) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I)  )  (=>  (add s3 s3r s1 s1r x a i s2 s2r) (and (not (c s3r x))(c s3 x )) )))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) ) (exists ((y T))  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s3 x) (c s1 x) ) (and (c s2 y) (not (c s2r y)) (not (c s3 y)) (not (c s1 y)) (= (elem y) a) (= (parent y) x) (= (ts y) i)  ) ) )))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (or (c s3r x)(not (c s3 x)) (not (c s1 x)) )) (= s1 s2) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s3r s1 s1r x a i s2 s2r) (c s2 y)) (or (c s1 y) (and (= (elem y) a) (= (parent y) x) (= (ts y) i) (c s3 x) (not (c s3r x)) (c s1 x) (not (c s3 y)))  ) ) ))
(assert (forall ((x T) (a A) (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (i I) (y T) )  (=>  (add s3 s3r s1 s1r x a i s2 s2r) (= s1r s2r) )))

(declare-fun remove(S S S S T S S) Bool)
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (remove s3 s3r s1 s1r x s2 s2r) (= s1 s2) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S) (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s3 x)) (c s2r x) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s1r y)) (c s2r y) ) ))
(assert (forall ((x T)  (s1 S) (s1r S) (s2r S) (s3r S) (s2 S)  (s3 S) (y T) ) (=> (and (remove s3 s3r s1 s1r x s2 s2r) (c s2r y)) (or (c s1r y) (and (= x y) (c s3 y)) ) ) ))

(declare-fun cl (S S T) Bool) ;Contains predicate for lisdt
(assert (forall ((s S) (sr S) (t T)) (= (cl s sr t) (and (c s t) (not (c sr t)) ) )  ))

(declare-fun apply (E S S S S) Bool)
(assert (forall ((e E) (s1 S) (s1r S) (s2 S) (s2r S)) (= (apply e s1 s1r s2 s2r)
  (ite (= (op e) Add) (add (src e) (srcr e) s1 s1r (argE e) (argN e) (eid e) s2 s2r ) (remove (src e) (srcr e) s1 s1r (argE e) s2 s2r ) ) ) ))

;Encoding of NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)
(declare-fun vis (E E) Bool)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (and (= (src e1p) s0) (= (srcr e1p) s0r) ) ))
(assert (=> (not (vis e1p e2p))  (and (= (src e2p) s0) (= (srcr e2p) s0r) ) ))


(assert (=> (vis e2p e1p) (apply e2p s0 s0r (src e1p) (srcr e1p) )   ) )
(assert (=> (vis e1p e2p) (apply e1p s0 s0r (src e2p) (srcr e2p))  ) )


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


(assert (apply pe11 s0 s0r se11 se11r))
(assert (apply pe12 se11 se11r se12 se12r))
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


(assert (apply pe21 s0 s0r se21 se21r))
(assert (apply pe22 se21 se21r se22 se22r)  )
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))
 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (cl se12 se12r a) (cl se22 se22r a))))

;Consistency Policy-PSI+RB
;Note that two add operations involve the same list element if the either of argument of the operations or the element inserted by the ;operations are the same
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2)))  ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (eid e1) (ts (argE e2)))  (vis e1 e2)) (eo e1 e2) ) ))



(check-sat)
(get-model)
