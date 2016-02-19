# Create HTML from my Org Notes

SOURCES=$(wildcard *.org)
OBJECTS=$(patsubst %.org,%.html,$(SOURCES))
ORG_VERSION=org-8.3.3
ORG_URL=http://orgmode.org/$ORG_VERSION.tar.gz

all: ../$(ORG_VERSION) $(OBJECTS)

../$(ORG_VERSION):
	cd .. && curl http://orgmode.org/org-8.3.3.tar.gz | tar xvz

%.html: %.org
	emacs --batch --eval "(add-to-list 'load-path \"../$(ORG_VERSION)/lisp/\")" --eval "(require 'org)" $< -f org-html-export-to-html --kill

