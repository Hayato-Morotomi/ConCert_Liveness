import re
import argparse
from pathlib import Path

# 日本語文字をざっくり検出
# ひらがな, カタカナ, CJK統合漢字, 半角カナを対象
JP_REGEX = re.compile(
    r"["
    r"\u3040-\u309F"  # ひらがな
    r"\u30A0-\u30FF"  # カタカナ
    r"\u3400-\u4DBF"  # CJK拡張A
    r"\u4E00-\u9FFF"  # CJK統合漢字
    r"\uFF66-\uFF9F"  # 半角カナ
    r"]"
)


def remove_jp_comments_rocq(content: str):
    """
    Rocq/Coq のネスト可能コメント (* ... *) を解析し、
    日本語を含むコメントブロックだけ削除します。

    文字列リテラル "..." の中にある (*, *) はコメントとして扱いません。
    文字列中の "" はエスケープされたダブルクォートとして扱います。

    戻り値:
      (new_content, changed, error)
      error is None なら成功です。
    """
    result = []
    i = 0
    n = len(content)

    depth = 0
    in_string = False
    comment_buf = []
    changed = False

    while i < n:
        char = content[i]
        two = content[i:i + 2]

        # コメント外・文字列内
        if depth == 0 and in_string:
            if two == '""':
                # Rocq/Coq 文字列中のエスケープされた "
                result.append('""')
                i += 2
            elif char == '"':
                in_string = False
                result.append(char)
                i += 1
            else:
                result.append(char)
                i += 1
            continue

        # コメント外・文字列外
        if depth == 0:
            if char == '"':
                in_string = True
                result.append(char)
                i += 1
            elif two == "(*":
                depth = 1
                comment_buf = ["(*"]
                i += 2
            else:
                result.append(char)
                i += 1
            continue

        # コメント内
        if two == "(*":
            depth += 1
            comment_buf.append("(*")
            i += 2
        elif two == "*)":
            depth -= 1
            comment_buf.append("*)")
            i += 2

            if depth == 0:
                comment = "".join(comment_buf)
                if JP_REGEX.search(comment):
                    # 行番号ずれを抑えるため改行数だけ維持
                    result.append("\n" * comment.count("\n"))
                    changed = True
                else:
                    result.append(comment)
                comment_buf = []
        else:
            comment_buf.append(char)
            i += 1

    if depth != 0:
        return content, False, "Unclosed comment detected"

    if in_string:
        return content, False, "Unclosed string detected"

    return "".join(result), changed, None


def process_file(path: Path, dry_run: bool = False, backup: bool = True):
    try:
        original_text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return "skip", f"Encoding Error: {path}"
    except OSError as e:
        return "skip", f"Read Error: {path} ({e})"

    new_text, changed, error = remove_jp_comments_rocq(original_text)

    if error is not None:
        return "skip", f"{error}: {path}"

    if not changed:
        return "unchanged", str(path)

    if dry_run:
        return "would_change", str(path)

    try:
        if backup:
            backup_path = path.with_suffix(path.suffix + ".bak")
            backup_path.write_text(original_text, encoding="utf-8")

        path.write_text(new_text, encoding="utf-8")
    except OSError as e:
        return "skip", f"Write Error: {path} ({e})"

    return "changed", str(path)


def iter_v_files(target_dir: Path):
    for path in target_dir.rglob("*.v"):
        if path.is_file():
            yield path


def main():
    parser = argparse.ArgumentParser(
        description="Remove Rocq/Coq comments containing Japanese text."
    )
    parser.add_argument(
        "target_dir",
        nargs="?",
        default=".",
        help="Directory to scan recursively (default: current directory)"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show files that would be modified without writing changes"
    )
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="Do not create .bak backup files"
    )
    args = parser.parse_args()

    target_dir = Path(args.target_dir)

    if not target_dir.exists():
        print(f"Error: target does not exist: {target_dir}")
        return

    if not target_dir.is_dir():
        print(f"Error: target is not a directory: {target_dir}")
        return

    processed_count = 0
    would_change_count = 0
    skipped_count = 0

    for path in iter_v_files(target_dir):
        status, message = process_file(
            path,
            dry_run=args.dry_run,
            backup=not args.no_backup
        )

        if status == "changed":
            print(f"Cleaned: {message}")
            processed_count += 1
        elif status == "would_change":
            print(f"Would clean: {message}")
            would_change_count += 1
        elif status == "skip":
            print(f"Skip: {message}")
            skipped_count += 1

    if args.dry_run:
        print(
            f"\n完了: {would_change_count} 個のファイルが変更対象です。"
            f" スキップ {skipped_count} 個。"
        )
    else:
        print(
            f"\n完了: {processed_count} 個のファイルを修正しました。"
            f" スキップ {skipped_count} 個。"
        )


if __name__ == "__main__":
    main()