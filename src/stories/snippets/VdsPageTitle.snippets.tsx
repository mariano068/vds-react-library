import { Link, Typography } from '@mui/material'
import * as React from 'react'
import { Highlight } from '../shared/Highlight'
import { VdsBreadcrumb } from '../../vds/VdsBreadcrumb/VdsBreadcrumb'
import { VdsPageTitle } from '../../vds/VdsPageTitle/VdsPageTitle'
import { convert } from '../utils'
import CodeHighlight from '../shared/CodeHighlight'

//#region Snippets
export const breadcrumb_snippet = convert(`
import React from 'react';
import { Breadcrumb } from 'vds-components';

export default () => {

    const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

    return (
      <VdsBreadcrumb>
        <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
        <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
        <Typography>Text 1</Typography>
        <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
        <Typography>Text 2</Typography>
      </VdsBreadcrumb>
    );
}
`)
//#endregion

//#region Examples
export const Breadcrumb_Default_Example = () => {

  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsBreadcrumb>
      <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
      <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
      <Typography>Text 1</Typography>
    </VdsBreadcrumb>
  )
}
export const PageTitle_WithDescription_Example = () => {

  const handleBackEvent = () => console.dir('click');

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content="Page description or explanation text"
    />
  )
}
export const PageTitle_WithBreadcrumb_Example = () => {

  const handleBackEvent = () => console.dir('click');
  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content={
        <VdsBreadcrumb>
          <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
          <Typography>Text 1</Typography>
        </VdsBreadcrumb>
      }
    />
  )
}
export const PageTitle_Default_Example = () => {

  return (
    <VdsPageTitle title="PAGE TITLE" />
  )
}
export const PageTitle_WithLongDescription_Example = () => {

  const handleBackEvent = () => console.dir('click');

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content="Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla in aliquam sapien. Suspendisse interdum accumsan tempus"
    />
  )
}
export const PageTitle_WithoutIcon_Example = () => {

  const handleBackEvent = () => console.dir('click');
  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content={
        <VdsBreadcrumb>
          <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 4</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 5</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 6</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 7</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 8</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 9</Link>
          <Typography>Text 1</Typography>
        </VdsBreadcrumb>
      }
    />
  )
}
//#endregion

export default () => (
  <>
    <VdsPageTitle title='Page Title' />
    <p>Page title defines a specific area, always placed on the top of the page and below the header, with specific information regarding the name of the page and all the navigation indication required (i.e. breadcrumb, page information, section title…).</p>
    <h3>Overview</h3>
    <p>Page title has 2 states: extended and reduced. By default, page titles are set to extended. The component is set to extended state until the user scrolls down and the title page component reaches the top margin of the window. The extended page title now changes into reduced state becoming a fixed element on top of the page. The space dedicated to page description or explaination text can also contain a breadcrumb to ease the navigation</p>
    <CodeHighlight>
      <PageTitle_Default_Example />
    </CodeHighlight>
    <CodeHighlight>
      <PageTitle_WithDescription_Example />
    </CodeHighlight>
    <CodeHighlight>
      <PageTitle_WithBreadcrumb_Example />
    </CodeHighlight>
    <CodeHighlight>
      <PageTitle_WithLongDescription_Example />
    </CodeHighlight>
    <CodeHighlight>
      <PageTitle_WithoutIcon_Example />
    </CodeHighlight>
  </>
)
