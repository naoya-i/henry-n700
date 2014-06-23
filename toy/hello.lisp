
(B (=> (unhappy x) (exam x) ) )
(B (=> (happy x) (exam x) ) )

(O (name happy) (label (^ (happy ?s) (exam ?s) (! (unhappy ?s) ) )) (^ (exam JOHN) ) )

; 
(O (name lingheu) (^ (john-nn x1) (kill-vb x1 x2) (mary-nn x3) (kill-vb x3 x4)) )
(O (name lingheu2) (^ (john-nn x1) (kill-vb x1 x2) (john-nn x3) (kill-vb x3 x4)) )

(B (=> (john-nn x) (man-nn x)) )
(O (name lingheu3) (^ (john-nn x1) (kill-vb x1 x2) (man-nn x3) (hate-vb x3 x4)) )

    (B (=> (^ (shopping x :0.6) (store y :0.6)) (go x y) ) )
    (B (=> (^ (robbing x :0.6) (store y :0.6))  (go x y) ) )
    (B (=> (^ (robbing x :0.6) (gun y :0.6)) (get x y) ) )
    (B (=> (^ (hunting x :0.6) (gun y :0.6)) (get x y) ) )

    (O (^ (get John g) (gun g) (go John s) (store s) ) )
