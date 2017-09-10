note

class
	TS_INTEGER_RELATION_TEST

feature

	pass1
		local
			a, b: TS_INTEGER_RELATION
		do
			create a.make_empty
			check not a.has (1, 2) end
			a.add (1, 2)
			check a.has (1, 2) end
			a.remove (1, 2)
			check not a.has (1, 2) end
		end



end
