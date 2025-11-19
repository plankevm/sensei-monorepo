import XCTest
import SwiftTreeSitter
import TreeSitterSensei

final class TreeSitterSenseiTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_sensei())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Sensei grammar")
    }
}
