(define (problem bt2)
(:domain bt)
(:requirements :strips :equality :typing :conditional-effects :disjunctive-preconditions)
(:objects b0 - bomb p0 p1 - package    t0  - toilet)
 (:init
(unknown (in p0 b0))
(unknown (in p1 b0))
 

 (notdefused b0)
;(not (clog t0))
(oneof (in p0 b0)
    (in p1 b0)
)
)

 (:goal (defused b0)))
