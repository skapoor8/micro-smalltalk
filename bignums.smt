(class Natural Magnitude
	(degree digitArray base)	

	(class-method new: (anInteger)
		(newInt: (new self) anInteger))


	(method newInt: (anInteger) (locals count digitList)
		(set base 10)
		(set count 0)
		(set digitList (new List))
		(whileTrue: {(> anInteger 0)}
			{
			(addLast: digitList (mod: anInteger base))
			(set anInteger (asInteger (/ anInteger base)))
			(set count (+ count 1))})
		(ifTrue: (= count 0)
			{(addLast: digitList 0)
			(set count 1)})
		(digits: self digitList)
		(set degree count)
		self)

	(method degree ()
		degree)

	(method base ()
		base)
	
	(method digit: (anIndex) ; 1-indexed
		(at: digitArray anIndex))

	(method digit:put: (anIndex aDigit) ; 1-indexed
		(at:put: digitArray anIndex aDigit))

	(method makeEmpty: (aDegree) (locals apply)
		(set apply (block (i) (digit:put: self i 0)))
		(set digitArray (new: Array aDegree))
		(set degree aDegree)
		(doDigits: self apply))

	(method doDigits: (aBlock) (locals i)
		(set i 0)
		(whileTrue: {(< i degree)}
			{(set i (+ i 1))
			(value aBlock i)}))

	(method trim () 
		(whileTrue: {(& (> degree 1) (= (at: digitArray degree) 0))}
		{(set degree (- degree 1))}))

	(method digits: (aSequence)
		(set degree (size aSequence))
		(if (= degree 0) 
			{(set degree 1)
		 	(set digitArray (new: Array 1))
		 	(at:put: digitArray 1 0)}
			{(set digitArray (from: Array aSequence))}))

	(method decimal () (locals i result)
		(set i degree)

		(set result (new List)) ; where?
		(whileTrue: {(> i 0)}

			{(addLast: result (at: digitArray i)) 
			(set i (- i 1))})
		result) ; return result list

	(method print () (locals digitList)
		(set digitList (decimal self))
		(do: digitList (block (x) (print x))))

	(method isZero ()
		(& (= degree 1) (= (at: digitArray 1) 0)))

	(method = (x) (locals apply isEqual)
		(set isEqual true)
		(if (= degree (degree x))
			{(set apply (block (i) (if (= (at: digitArray i) (digit: x i))
				{(set isEqual (& isEqual true))}
				{(set isEqual (& isEqual false))})))
			(doDigits: self apply)}

			{(set isEqual false)})
		isEqual)

	(method set:plus: (x y) (locals apply xi yi sum resultDegree carry)
		(set carry 0)
		(set apply (block (i) 
			(if (> i (degree y))
				{(set yi 0)}
				{(set yi (digit: y i))})
			(if (> i (degree x))
				{(set xi 0)}
				{(set xi (digit: x i))})
			(set sum (+ (+ xi yi) carry))
			(at:put: digitArray i (mod: sum base))
			(set carry (asInteger (/ sum base)))))
		(if (>= (degree x) (degree y))
			{(if (= degree (+ (degree x) 1))
				{(set degree (+ (degree x) 1))
				(doDigits: self apply)
				self}
				{(error: self #ill-fitted-receiver)})}
			{(set:plus: self y x)}))

	(method set:minus: (x y) (locals borrow apply diff resultDegree isValid xi yi)
		(set borrow 0)
		(set apply (block (i) 
			(if (> i (degree y))
				{(set yi 0)}
				{(set yi (digit: y i))})
			(set xi (digit: x i))
			(ifTrue: (> yi xi)
				{(if (= i degree)
					{(set borrow 1)}
					{(set xi (+ base xi))
					(digit:put: x (+ i 1) (- (digit: x (+ i 1)) 1))})})
			(set diff (- xi yi))
			(at:put: digitArray i diff)))

		(if (>= (degree x) (degree y)) 
			{(if (= degree (degree x))
				{(set resultDegree degree)
				(makeEmpty: self resultDegree)
				(doDigits: self apply)
				(set degree resultDegree)
				(trim self)}
				{(error: self #ill-fitted-receiver)})}
			{(set borrow 1)})
		borrow)

	(method + (x) (locals deg result)
		(if (>= degree (degree x))
			{(set deg (+ (degree self) 1))}
			{(set deg (+ (degree x) 1))})
		(set result (new: Natural 0))
		(makeEmpty: result deg)
		(set:plus: result self x)
		(trim result)
		result)

	(method subtract:withDifference:ifNegative: (aNatural diffBlock negativeBlock) 
		(locals result borrow deg)
		(ifFalse: (>= degree (degree aNatural))
			{(value negativeBlock)})
		(set result (new: Natural 0))
		(makeEmpty: result degree)
		(set borrow (set:minus: result self aNatural))
		(if (= borrow 0)
			{(trim result)
			(value diffBlock result)}
			{(value negativeBlock)}))

	(method - (x) (locals result diff negative )
		(set diff (block (z) z))
		(set negative {(error: self #difference-not-a-natural-number)})
		(subtract:withDifference:ifNegative: self x diff negative))

	; (method - (x) (locals result borrow deg)
	; 	(ifFalse: (>= degree (degree x))
	; 		{(error: self #difference-not-a-natural-number)})
	; 	(set result (new: Natural 0))
	; 	(makeEmpty: result degree)
	; 	(set borrow (set:minus: result self x))
	; 	(if (= borrow 0)
	; 		{(trim result)
	; 		(decimal result)}
	; 		{(error: self #difference-not-a-natural-number)})
	; 	)

	(method set:multiply: (x y) (locals i j carry)
		(ifFalse: (= degree (+ (degree x) (degree y)))
			{(error: self #ill-fitted-receiver)})
		;(set carry 0)
		(makeEmpty: self degree)
		(set i 0)
		; (println self)
		; (println degree)
		; (println #x-is)
		; (println x)
		; (println #y-is)
		; (println y)
		; (println #deg-x-is)
		; (println (degree x))
		; (println #deg-y-is)
		; (println (degree y))
		(whileTrue: {(< i (degree x))}
			{(set carry 0)
			(set j 0)
			(whileTrue: {(< j (degree y))}
				{(set carry (+ carry (+ (* (digit: x (+ i 1)) (digit: y (+ j 1))) (digit: self (+ (+ i j) 1)))))
				(digit:put: self (+ (+ i j) 1) (mod: carry base))
				(set carry (asInteger (/ carry base)))
				(set j (+ j 1))})
			(digit:put: self (+ (+ i j) 1) carry)
			(set i (+ i 1))})
		;carry
		self)

	(method * (x) (locals result)
		(set result (new: Natural 0))
		(makeEmpty: result (+ (degree x) degree))
		(set:multiply: result self x)
		(trim result)
		result)

	(method < (x) (locals result diff negative)
		(set diff (block (x) false))
		(set negative {true})
		(subtract:withDifference:ifNegative: self x diff negative))


)






