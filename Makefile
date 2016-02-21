SOURCES=$(wildcard *.org)
OBJECTS=$(patsubst %.org,%.html,$(SOURCES))

all: $(OBJECTS)

%.html: %.org
	emacs --batch -eval "(add-to-list 'load-path \"./\")" -eval "(setq org-html-htmlize-output-type 'css)" -eval "(require 'org)" -eval "(setq org-html-htmlize-font-prefix \"org-\")" -eval "(require 'coq)" $< -f org-html-export-to-html --kill
