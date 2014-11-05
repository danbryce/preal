(define (domain simple)
(:predicates (p))


(:action mp
 :precondition (p)
 :effect (not (p)))


) 
