package tree_sitter_sensei_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_sensei "github.com/senseilang/sensei-tree-sitter/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_sensei.Language())
	if language == nil {
		t.Errorf("Error loading Sensei grammar")
	}
}
