note
	explicit: wrapping, contracts

class
	TS_INTEGER_PAIR

inherit

	ANY
		redefine
			is_equal
		end

create
	make

feature -- Initialization

	make (a_left, a_right: INTEGER)
		note
			status: creator
		require
--			is_open
		do
			left := a_left
			right := a_right
			wrap
		ensure
			left = a_left
			right = a_right
			is_wrapped
		end

feature -- Storage

	left, right: INTEGER

feature -- Comparison

	same_values (a_left, a_right: INTEGER): BOOLEAN
		require
--			closed
			reads_field(["left", "right"], Current)
		do
			Result := (left = a_left) and (right = a_right)
		ensure
			Result = ((left = a_left) and (right = a_right))
		end

	is_equal (a_other: TS_INTEGER_PAIR): BOOLEAN
		require else
--			closed
--			a_other.closed
			reads_field(["left", "right"], [Current, a_other])
		do
			Result := a_other.same_values (left, right)
		ensure then
			Result = a_other.same_values (left, right)
			Result = same_values (a_other.left, a_other.right)
			reflexive: a_other = Current implies Result
			symmetric: Result = a_other.is_equal (Current)
		end

invariant

	True


end
