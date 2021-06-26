module CommonParsing (parse_id, parse_number, parseMaybe, parse_until_chs, parse_ls_ids) where

import Text.ParserCombinators.ReadP

is_letter::Char->Bool
is_letter ch = (ch>='a' && ch<='z') || (ch>='A' && ch<='Z')

is_digit::Char->Bool
is_digit ch = (ch>='0' && ch<='9') 

is_val_id_char::Char->Bool
is_val_id_char ch = is_letter ch || is_digit ch || ch == '_'

parse_number::ReadP String
parse_number = do
   n<- (many1 . satisfy) is_digit
   return n

parse_fst_letter_of_id ::ReadP String
parse_fst_letter_of_id = do
   ch<- satisfy (is_letter)
   return (ch:"")

parse_id::ReadP String
parse_id = do
   id <- parse_fst_letter_of_id 
   str<-(munch is_val_id_char)
   return (id++str)

parseMaybe :: ReadP a -> String -> Maybe a
parseMaybe parser input =
    case readP_to_S parser input of
        [] -> Nothing
        ((result, _):_) -> Just result

parse_until_chs::String->ReadP String
parse_until_chs chs = do
    str<-munch (\ch-> all (ch /=) chs)
    return str

parse_ls_ids ::String->String->ReadP [String]
parse_ls_ids ts sep = do
   ps<-sepBy (parse_until_chs ts) (satisfy (\ch->any (ch==) sep))
   return ps