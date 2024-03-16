;Cleaner Domain: rooms = 2

(define (domain cleaner)
  (:predicates
	(ROOM ?r)
	(OBJECT ?o)
	(position ?x)
	(cleaned ?r ?o)
	)
	(:action clean
	:parameters (?r ?o)
	:precondition (and (OBJECT ?o) (ROOM ?r))
	:effect (when (position ?r) (cleaned ?r ?o)))
	(:action fwd
	:parameters ()
	:effect (and
		(when (position r0) (and (position r1) (not (position r0))))
))
	(:action back
	:parameters ()
	:effect (and
		(when (position r1) (and (position r0) (not (position r1))))
)))
