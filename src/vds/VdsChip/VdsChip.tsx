import { IconButton } from "@mui/material";
import * as React from "react";
import { IoIosClose } from "react-icons/io";

function htmlToText(html: any) {
    var temp = document.createElement('div');
    temp.innerHTML = html;
    return temp.textContent;
}

export const VdsChip = ({ label, onDelete, disabled }: any) => {
    return (
        <div style={{
            fontSize: "12px",
            color: "#005075",
            letterSpacing: "0",
            lineHeight: "24px",
            fontFamily: "Cairo SemiBold",
            fontWeight: 600,
            textAlign: "left",
            padding: '0px 0px 0px 16px',
            borderRadius: '4px',
            backgroundColor: '#DEF0F7',
            display: 'flex',
            alignItems: 'center',
            margin: 2,
            paddingRight: onDelete ? 0 : '16px'
        }}>
            {htmlToText(label)}{onDelete && (<IconButton disabled={disabled} sx={{
                padding: 0,
                color: "#005075 !important",
                fill: "#005075 !important",
                fontSize: "19.5px",
                letterSpacing: "0",
                textAlign: "center",
                fontWeight: 400,
                marginLeft: '5px',
                ':hover': {
                    backgroundColor: 'unset',
                    opacity: 'unset'
                }
        }}
            onClick={() => {
                onDelete();
            }}
            ><IoIosClose /></IconButton>)}
        </div>
    );
}
