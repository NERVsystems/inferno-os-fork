Asyncio: module {
	PATH: con "/dis/xenith/asyncio.dis";

	init: fn(mods: ref Dat->Mods);

	# Async operation messages sent to casync channel
	AsyncMsg: adt {
		pick {
			Chunk =>
				opid: int;      # Operation ID
				data: string;   # Chunk of data read
				offset: int;    # Position in file
			Progress =>
				opid: int;
				current: int;   # Bytes processed so far
				total: int;     # Total bytes (0 if unknown)
			Complete =>
				opid: int;
				nbytes: int;    # Total bytes read
				nrunes: int;    # Total runes (characters)
				err: string;    # nil on success
			Error =>
				opid: int;
				err: string;
			ImageData =>
				opid: int;
				winid: int;     # Window ID for the image
				path: string;   # Image path (for display in tag)
				data: array of byte;  # Raw image bytes
				err: string;    # nil on success
		ImageDecoded =>
				winid: int;     # Window ID for the image
				path: string;   # Image path (for display in tag)
				image: ref Draw->Image;  # Decoded image (nil on error)
				err: string;    # nil on success
		TextData =>
				opid: int;      # Operation ID
				winid: int;     # Window ID for the text
				path: string;   # File path
				q0: int;        # Insert position (start of file content)
				data: string;   # Chunk of text data
				offset: int;    # Rune offset within file (cumulative)
				err: string;    # nil on success
		TextComplete =>
				opid: int;      # Operation ID
				winid: int;     # Window ID for the text
				path: string;   # File path
				nbytes: int;    # Total bytes read
				nrunes: int;    # Total runes read
				err: string;    # nil on success
		}
	};

	# Async operation handle for cancellation
	AsyncOp: adt {
		opid: int;
		ctl: chan of int;   # Send 1 to cancel
		path: string;
		active: int;
		winid: int;         # Window ID (for image ops)
	};

	# Start async file read - returns operation handle
	asyncload: fn(path: string, q0: int): ref AsyncOp;

	# Start async image load - returns operation handle
	asyncloadimage: fn(path: string, winid: int): ref AsyncOp;

	# Start async text file load - returns operation handle
	asyncloadtext: fn(path: string, q0: int, winid: int): ref AsyncOp;

	# Cancel an async operation
	asynccancel: fn(op: ref AsyncOp);

	# Check if operation is still active
	asyncactive: fn(op: ref AsyncOp): int;

	# Note: Results are sent to dat->casync channel
};
