(set-logic LIA)

(declare-var y Int)
(declare-var y! Int)
(declare-var x Int)
(declare-var x! Int)
(declare-var tmp Int)
(declare-var tmp! Int)
(declare-var j Int)
(declare-var j! Int)
(declare-var i Int)
(declare-var i! Int)
(declare-var flag Int)
(declare-var flag! Int)

(declare-var y_37 Int)
(declare-var y_25 Int)
(declare-var y_20 Int)
(declare-var x_36 Int)
(declare-var x_24 Int)
(declare-var x_19 Int)
(declare-var j_34 Int)
(declare-var j_28 Int)
(declare-var j_27 Int)
(declare-var j_21 Int)
(declare-var i_33 Int)
(declare-var i_26 Int)
(declare-var i_22 Int)
(declare-var flag_0 Int)

(synth-fun inv-f((flag Int)(i Int)(j Int)(tmp Int)(x Int)(y Int)) Bool
  (
    (StartInt Int
      ( flag i j tmp x y 0 1
        (+ StartInt StartInt)
        (- StartInt StartInt)
        (* StartInt StartInt)
      )
    )
    (Start Bool
      (
        (not Start)
        (and Start Start)
        (or Start Start)
        (< StartInt StartInt)
        (<= StartInt StartInt)
        (= StartInt StartInt)
        (> StartInt StartInt)
        (>= StartInt StartInt)
      )
    )
  )
)

(define-fun pre-f ((flag Int)(i Int)(j Int)(tmp Int)(x Int)(y Int)(flag_0 Int)(i_22 Int)(i_26 Int)(i_33 Int)(j_21 Int)(j_27 Int)(j_28 Int)(j_34 Int)(x_19 Int)(x_24 Int)(x_36 Int)(y_20 Int)(y_25 Int)(y_37 Int)) Bool
  (and
    (= y y_20)
    (= x x_19)
    (= j j_21)
    (= i i_22)
    (= x_19 0)
    (= y_20 0)
    (= j_21 0)
    (= i_22 0)
  )
)

(define-fun trans-f ((flag Int)(i Int)(j Int)(tmp Int)(x Int)(y Int)(flag! Int)(i! Int)(j! Int)(tmp! Int)(x! Int)(y! Int)(flag_0 Int)(i_22 Int)(i_26 Int)(i_33 Int)(j_21 Int)(j_27 Int)(j_28 Int)(j_34 Int)(x_19 Int)(x_24 Int)(x_36 Int)(y_20 Int)(y_25 Int)(y_37 Int)) Bool
  (or 
    (and
      (= i_33 i)
      (= j_34 j)
      (= x_36 x)
      (= y_37 y)
      (= y_37 y!)
      (= x_36 x!)
      (= j_34 j!)
      (= i_33 i!)

      (= y y!)
      (= x x!)
      (= tmp tmp!)
      (= j j!)
      (= i i!)
      (= flag flag!)
    )
    (and
      (= i_33 i)
      (= j_34 j)
      (= x_36 x)
      (= y_37 y)
      (= x_24 (+ x_36  1))
      (= y_25 (+ y_37  1))
      (= i_26 (+ i_33  x_24))
      (= j_27 (+ j_34  y_25))
      (not (> flag_0  0))
      (= y_25 y!)
      (= x_24 x!)
      (= j_27 j!)
      (= i_26 i!)

      (= flag flag_0)
      (= flag! flag_0)
      (= tmp tmp!)
    )
    (and
      (= i_33 i)
      (= j_34 j)
      (= x_36 x)
      (= y_37 y)
      (= x_24 (+ x_36  1))
      (= y_25 (+ y_37  1))
      (= i_26 (+ i_33  x_24))
      (= j_27 (+ j_34  y_25))
      (> flag_0  0)
      (= j_28 (+ j_27  1))
      (= y_25 y!)
      (= x_24 x!)
      (= j_28 j!)
      (= i_26 i!)

      (= flag flag_0)
      (= flag! flag_0)
      (= tmp tmp!)
    )

  )
)

(define-fun post-f ((flag Int)(i Int)(j Int)(tmp Int)(x Int)(y Int)(flag_0 Int)(i_22 Int)(i_26 Int)(i_33 Int)(j_21 Int)(j_27 Int)(j_28 Int)(j_34 Int)(x_19 Int)(x_24 Int)(x_36 Int)(y_20 Int)(y_25 Int)(y_37 Int)) Bool
  (and
    (and
      (= i i_33)
      (= j j_34)
      (not
        (and

          (not (>= j_34  i_33))
        )
      )
    )

  )

)

(constraint
  (=>
    (pre-f flag i j tmp x y flag_0 i_22 i_26 i_33 j_21 j_27 j_28 j_34 x_19 x_24 x_36 y_20 y_25 y_37 )
    (inv-f flag i j tmp x y )
  )
)
(constraint
  (=>
    (and
      (inv-f flag i j tmp x y )
      (trans-f flag i j tmp x y flag! i! j! tmp! x! y! flag_0 i_22 i_26 i_33 j_21 j_27 j_28 j_34 x_19 x_24 x_36 y_20 y_25 y_37 )
    )
    (inv-f flag! i! j! tmp! x! y! )
  )
)
(constraint
  (=>
    (inv-f flag i j tmp x y )
    (post-f flag i j tmp x y flag_0 i_22 i_26 i_33 j_21 j_27 j_28 j_34 x_19 x_24 x_36 y_20 y_25 y_37 )
  )
)

(check-synth)
