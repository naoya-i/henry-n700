
(B (name shopperGoes) (=>
  (^ (plan-shopping x :0.6) (at x y :0.0) (store y :0.6))
  (go-to x y)
))

(B (name robberGoes) (=> (^ (plan-robbing x :0.6) (at x y :0.0) (store y :0.6))  (go-to x y) ) )
(B (name robberUses) (=> (^ (plan-robbing x :0.6) (uses x y :0.0) (gun y :0.6)) (get x y) ) )
(B (name hunterUses) (=> (^ (plan-hunting x :0.6) (uses x y :0.0) (gun y :0.6)) (get x y) ) )

; Observation
(O (^ (get John g) (gun g) (go-to John s) (store s) ) )
