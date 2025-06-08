SHELL := /bin/bash
DIRS := skipSpace skipSpaceAndComma skipEscape skipAnyLiteral skipUTF8
DIRS += skipNumber skipString skipCollection JSON_Validate JSON_Search
DIRS += JSON_Iterate

PROOF_COMMANDS := cbmc goto-cc goto-instrument goto-analyzer cbmc-viewer
SHELL_COMMANDS := mawk sed w3m

# run all the proofs in ascending dependency order
# and show a summary page for each
all: precheck clean
	for d in $(DIRS); do \
		echo -n $$d; \
		time make -C $$d 2>&1 | mawk -W interactive 'NR % 30 == 0 {printf "."}'; echo; \
		w3m -cols 120 -dump $$d/html/index.html | sed 's/^/        /'; \
	done

clean:
	for d in $(DIRS); do make -C $$d cleanclean >/dev/null 2>&1; done

precheck:
	@hash $(PROOF_COMMANDS) $(SHELL_COMMANDS)

.PHONY: all clean precheck
