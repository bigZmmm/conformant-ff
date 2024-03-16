(define (domain blocks)
  (:requirements :typing)
  (:types block)
  (:predicates (on ?x - block ?y - block)
	       (ontable ?x - block)
	       (clear ?x - block)
	       (handempty)
	       (holding ?x - block)
  )
  (:action pick-up
    :parameters (?x - block)
    :effect
      (when (and (handempty) (clear ?x) (ontable ?x))
        (and (not (ontable ?x))
             (not (clear ?x))
             (not (handempty))
             (holding ?x))
      )
  )
  (:action put-down
    :parameters (?x - block)
    :effect (when (holding ?x) (and (not (holding ?x)) (clear ?x) (handempty) (ontable ?x)))
  )
  (:action stack
    :parameters (?x - block ?y - block)
    :effect
      (when (and (holding ?x) (clear ?y))
        (and (not (holding ?x))
             (not (clear ?y))
             (clear ?x)
             (handempty)
             (on ?x ?y))
      )
  )
  (:action unstack
    :parameters (?x - block ?y - block)
    :effect
      (when (and (handempty) (on ?x ?y) (clear ?x))
        (and (holding ?x)
             (clear ?y)
             (not (clear ?x))
             (not (handempty))
             (not (on ?x ?y)))
      )
   )
)
