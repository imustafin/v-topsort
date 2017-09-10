note
	description: "Summary description for {TS_INTEGER_TOPOLOGICAL_SORTER_TEST}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	TS_INTEGER_TOPOLOGICAL_SORTER_TEST

feature

	pass1
		local
			s: TS_INTEGER_TOPOLOGICAL_SORTER
		do
			create s.make_empty
			s.add (1, 2)
			s.add (2, 3)
			s.topsort
			check s.sorted.count = 1 end
		end


end
