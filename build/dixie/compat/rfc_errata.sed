# Source fixes applied (by build.sh) to a COPY of src/ in gen/.  src/ itself is
# the verbatim RFC 6386 extraction.  Each fix is a typo in the RFC text that
# makes the code not compile / be meaningless; none changes intended semantics.
#
# tokens.c, vp8_dixie_tokens_process_row: RFC text reads
#     short              coeffs = tokens->coeffs + 25 * 16 * start_col;
# coeffs is used as a pointer (memset(coeffs,...), coeffs += 25*16, passed as
# short*), so it must be `short *coeffs` (as in libvpx's dixie tree).  Modern
# clang rejects the int<->pointer conversion; older compilers would silently
# truncate the pointer to 16 bits.
s/^\(    short  *\)coeffs = tokens->coeffs + 25 \* 16 \* start_col;/    short             *coeffs = tokens->coeffs + 25 * 16 * start_col;/
