(define (problem run-generator2)
    (:domain generator)
    (:objects gen - generator ;tank1 ;tank2 tank3 tank4
     - tank)
    (:init 	(= (fuelLevel gen)  1000)
		(= (capacity gen)  1600)
;		(available tank1)
;		(available tank2)
;		(available tank3)
;		(available tank4)
     )  
     (:goal (and (generator-ran) ))
) 
