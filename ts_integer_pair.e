class
	TS_INTEGER_PAIR

create
	make

feature -- Initialization

	make (a_left, a_right: INTEGER)
		note
			status: creator
		do
			left := a_left
			right := a_right
		ensure
			left = a_left
			right = a_right
		end

feature -- Values

	left, right: INTEGER

feature -- Comparison

	same_values (a_left, a_right: INTEGER): BOOLEAN
		note
			status: functional
		require
			reads_field(["left", "right"], Current)
		do
			Result := left = a_left and right = a_right
		end

end
