note
	description: "Summary description for {TS_INTEGER_PAIR_TEST}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	TS_INTEGER_PAIR_TEST

feature

	pass1
		local
			a, b, c: TS_INTEGER_PAIR
		do
			create a.make (1, 1)
			create b.make (2, 2)
			create c.make (1, 1)
			check not a.same_values (2, 2) end
			check a.same_values (1, 1) end
			check a.same_values (c.left, c.right) end
			check a.is_equal (c) end
			check c.is_equal (a) end
			check not a.is_equal (b) end
		end

end
