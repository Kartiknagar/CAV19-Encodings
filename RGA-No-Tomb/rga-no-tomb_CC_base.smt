;Encoding NON-INTERF-1

;Coming from the CRDT
(declare-sort T) ;Tuple
(declare-sort S) ;Set
(declare-sort A) ;List Element
(declare-datatypes () ((OpType (Add) (R))))

;Coming from the verification framework
(declare-sort E) ;Event
(declare-sort I) ;Event-Id

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
(declare-const start T)
(declare-fun c (S T) Bool)

(assert (c s0 start))
(assert (forall ((t T)) (=> (not (= t start)) (not (c s0 t)) ) ))

(declare-fun tso (I I) Bool)
(assert (forall ((t1 I) (t2 I) (t3 I)) (=> (and (tso t1 t2) (tso t2 t3)) (tso t1 t3) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (not (= t1 t2)) (or (tso t1 t2) (tso t2 t1)) ) ))
(assert (forall ((t1 I) (t2 I)) (=> (tso t1 t2) (not (tso t2 t1)) ) ))

(assert (forall ((t T)) (=> (not (= t start)) (tso (ts start) (ts t) ) ) ))
(assert (forall ( (t1 T) (t2 T)) (=>  (= (ts t1) (ts t2))  (= t1 t2) ) ))

;Encoding the RGA CRDT with no tomb-stones
(declare-fun add (S S T A I S) Bool)
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s1 y)) (c s2 y) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s3 y)) (tso (ts y) i) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=>  (add s3 s1 x a i s2) (c s3 x ) )))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) ) (exists ((y T))  (=> (and (add s3 s1 x a i s2) (c s3 x) (c s1 x) ) (and (c s2 y) (not (c s3 y)) (not (c s1 y)) (= (elem y) a) (= (parent y) x) (= (ts y) i)  ) ) )))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) )  (=> (and (add s3 s1 x a i s2) (or (not (c s3 x)) (not (c s1 x)) )) (= s1 s2) ) ))
(assert (forall ((x T) (a A) (s1 S) (s2 S) (s3 S) (i I) (y T) )  (=> (and (add s3 s1 x a i s2) (c s2 y)) (or (c s1 y) (and (= (elem y) a) (= (parent y) x) (= (ts y) i) (c s3 x) (c s1 x) (not (c s3 y)))  ) ) ))


(declare-fun remove(S S T S) Bool)
(assert (forall ((x T)  (s1 S) (s2 S) (s3 S) (y T) ) (=> (remove s3 s1 x s2) (= (c s2 y) (ite (and (c s3 x) (= x y)) false (c s1 y) )) ) ))


;Encoding of NON-INTERF-1 begins
(declare-const e1p E)
(declare-const e2p E)
(declare-fun vis (E E) Bool)

(assert (not (= e1p e2p)))

(assert (=> (not (vis e2p e1p))  (= (src e1p) s0) ))
(assert (=> (not (vis e1p e2p))  (= (src e2p) s0) ))



(assert (=> (vis e2p e1p) (ite (= (op e2p) Add) (add (src e2p) s0 (argE e2p) (argN e2p) (eid e2p)  (src e1p))
  (remove (src e2p) s0 (argE e2p) (src e1p) )   ) ))
(assert (=> (vis e1p e2p) (ite (= (op e1p) Add) (add (src e1p) s0 (argE e1p) (argN e1p) (eid e1p)  (src e2p))
  (remove (src e1p) s0 (argE e1p) (src e2p) )   ) ))


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

(assert (ite (= (op pe21) Add) (add (src pe21) s0 (argE pe21) (argN pe21) (eid pe21) se21) (remove (src pe21) s0 (argE pe21) se21) ))
(assert  (ite (= (op pe22) Add) (add (src pe22) se21 (argE pe22) (argN pe22) (eid pe22) se22) (remove (src pe22) se21 (argE pe22) se22) ))
(assert (eoe2 pe21 pe22))
(assert (not (eoe2 pe22 pe21)))

 (assert (forall ((e1 E) (e2 E) (e3 E)) (=> (and (eoe2 e1 e2) (eoe2 e2 e3)) (eoe2 e1 e3) ) ))
 (assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
 (assert (forall ((e E)) (not (eoe2 e e)) ))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const a T)
(assert  (not (= (c se12 a) (c se22 a))))

;Consistency Policy-CC
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((x1 E) (x2 E) (x3 E)) (=> (and (vis x1 x2) (vis x2 x3)) (vis x1 x3) ) ))
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (eo e1 e2) ) ))


(check-sat)
(get-model)
